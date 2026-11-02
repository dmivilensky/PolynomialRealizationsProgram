import jacobi.Laguerre.Polynomial
import jacobi.Jacobi.MehlerHeine

/-!
Article: jacobi, Proposition 6.1.
The actual classical normalized Laguerre polynomial at z/(4*n)
converges uniformly on every complex closed ball to the original
normalized Bessel function. A bounded finite descending-factorial
correction gives a common summable majorant for all degrees.
Source: DLMF 18.11.6, proved directly from the terminating coefficients.
Use: scaled_coefficient compares the genuine classical Laguerre polynomial with the existing Bessel coefficients.
-/
namespace jacobi.Laguerre
noncomputable section
open Polynomial Real Set Filter
open scoped BigOperators Topology
set_option backward.isDefEq.respectTransparency false

/-- The actual descending-factorial correction in the Laguerre-to-Bessel coefficient comparison.
Use: scaled_coefficient compares the genuine classical Laguerre polynomial with the existing Bessel coefficients.
Article: jacobi, Proposition 6.1.
-/
def correction (n k:ℕ) : ℝ := ∏j∈Finset.range k,(1-(j:ℝ)/n)

/-- The finite correction is its literal descending factorial divided by the degree power.
Use: scaled_coefficient matches the exact Laguerre and Bessel coefficients before passing to a limit.
Article: jacobi, Proposition 6.1.
Proof: below the terminating factor, cast the genuine natural subtraction in the descending-factorial recurrence. Beyond it both products vanish. -/
theorem correction_desc {n:ℕ} (hn:0<n) (k:ℕ) :
    correction n k=(n.descFactorial k:ℝ)/(n:ℝ)^k := by
  -- The subtraction casts correctly before termination; afterwards the true descending factorial is zero.
  have hn0:(n:ℝ)≠0 := Nat.cast_ne_zero.mpr hn.ne'
  induction k with
  | zero => simp [correction]
  | succ k ih =>
    rw [correction,Finset.prod_range_succ,← correction,ih,Nat.descFactorial_succ,Nat.cast_mul]
    by_cases hk:k≤n
    · rw [Nat.cast_sub hk,pow_succ]
      field_simp [hn0]
    · rw [Nat.descFactorial_eq_zero_iff_lt.mpr (lt_of_not_ge hk),Nat.cast_zero,zero_div,mul_zero,zero_mul,zero_div]

/-- The actual finite Laguerre correction terminates after its polynomial degree.
Use: normalized_scaled_eq_tsum restores the original finite polynomial as an infinite series with a genuinely zero tail.
Article: jacobi, Proposition 6.1.
Proof: its actual descending factorial is zero past degree n. -/
theorem correction_terminates {n k:ℕ} (hn:0<n) (hk:n<k) : correction n k=0 := by
  rw [correction_desc hn,Nat.descFactorial_eq_zero_iff_lt.mpr hk,Nat.cast_zero,zero_div]

/-- Every actual finite correction lies between zero and one, uniformly over all positive degrees and coefficient indices.
Use: scaling_error_limit has the original Bessel coefficient norm series as a summable common majorant.
Article: jacobi, Proposition 6.1.
Proof: before termination every factor 1-j/n is in [0,1]; after termination the original product is zero. -/
theorem correction_bounds {n:ℕ} (hn:0<n) (k:ℕ) : 0≤correction n k ∧ correction n k≤1 := by
  -- Positive product factors handle the finite degree range; the actual terminating factor handles the whole tail.
  by_cases hk:k≤n
  · have hf (j:ℕ) (hj:j∈Finset.range k) : 0≤1-(j:ℝ)/n ∧ 1-(j:ℝ)/n≤1 := by
      have hjn:(j:ℝ)≤n := by exact_mod_cast (Finset.mem_range.mp hj).le.trans hk
      have hp:(0:ℝ)<n := Nat.cast_pos.mpr hn
      constructor
      · exact sub_nonneg.mpr ((div_le_one hp).mpr hjn)
      · linarith [div_nonneg (Nat.cast_nonneg (α:=ℝ) j) hp.le]
    exact ⟨Finset.prod_nonneg (fun j hj=>(hf j hj).1),
      Finset.prod_le_one₀ (fun j hj=>(hf j hj).1) (fun j hj=>(hf j hj).2)⟩
  · rw [correction_terminates hn (lt_of_not_ge hk)]
    norm_num

/-- At every fixed coefficient degree the actual descending-factorial correction tends to one.
Use: scaling_error_limit gives the true compact uniform Laguerre-to-Bessel limit, rather than only a formal coefficient comparison.
Article: jacobi, Proposition 6.1.
Proof: reciprocal degree tends to zero, and finite products preserve the limits of the actual factors. -/
theorem correction_limit (k:ℕ) : Tendsto (fun n:ℕ=>correction n k) atTop (𝓝 1) := by
  have hi:Tendsto (fun n:ℕ=>(n:ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hf (j:ℕ) : Tendsto (fun n:ℕ=>1-(j:ℝ)/n) atTop (𝓝 1) := by
    simpa only [mul_zero,sub_zero,div_eq_mul_inv] using
      (tendsto_const_nhds (x:=(1:ℝ))).sub (hi.const_mul (j:ℝ))
  simpa only [correction,Finset.prod_const_one] using tendsto_finsetProd _ (fun j _=>hf j)

/-- The literal real rising factorial has the same value after inclusion in the complex field.
Use: scaled_coefficient compares the actual real Laguerre polynomial with the original complex Bessel function without changing normalizations.
Article: jacobi, Proposition 6.1.
Proof: the two actual rising-factorial recurrences agree under the real field inclusion. -/
theorem pochhammer_cast (a:ℝ) (k:ℕ) :
    (((ascPochhammer ℝ k).eval (a+1):ℝ):ℂ)=(ascPochhammer ℂ k).eval ((a:ℂ)+1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [ascPochhammer_succ_eval,ascPochhammer_succ_eval]
    push_cast
    rw [ih]

/-- Every actual scaled classical Laguerre coefficient equals the original Bessel coefficient times its genuine finite correction.
Use: normalized_scaled_eq_tsum identifies the entire actual finite polynomial with the corrected Bessel series.
Article: jacobi, Proposition 6.1.
Proof: use the actual Bessel Pochhammer formula and the proved
descending-factorial identity k!*binomial(n,k). Only actual positive
degree, factorial and order-normalization denominators are cancelled. -/
theorem scaled_coefficient {a:ℝ} (ha:-1<a) {n:ℕ} (hn:0<n) (k:ℕ) (z:ℂ) :
    (coefficient a n k:ℂ)*(z/(4*(n:ℂ)))^k=
      jacobi.Bessel.coefficient (a:ℂ) k*z^k*(correction n k:ℂ) := by
  -- The equality is exact at each finite degree, including the genuine terminated tail.
  have hP := jacobi.Bessel.pochhammer_ne_zero (a:=(a:ℂ)) (by simpa using ha) k
  have hF:(k.factorial:ℂ)≠0 := by exact_mod_cast Nat.factorial_ne_zero k
  have hN:(n:ℂ)≠0 := by exact_mod_cast hn.ne'
  rw [jacobi.Bessel.coefficient_pochhammer (by simpa using ha),correction_desc hn,
    Nat.descFactorial_eq_factorial_mul_choose]
  simp only [coefficient,Complex.ofReal_div,Complex.ofReal_mul,Complex.ofReal_pow,
    Complex.ofReal_neg,Complex.ofReal_one,Complex.ofReal_natCast,pochhammer_cast]
  rw [div_pow,mul_pow,div_pow]
  field_simp [hP,hF,hN]
  push_cast
  ring

/-- The original scaled finite Laguerre polynomial is exactly the corrected entire Bessel coefficient series.
Use: scaled_error_le bounds the actual polynomial, so its uniform limit does not depend on an auxiliary approximating family.
Article: jacobi, Proposition 6.1.
Proof: evaluate the actual terminating polynomial, use the exact
coefficient identity and restore only genuinely vanishing terms after degree n. -/
theorem normalized_scaled_eq_tsum {a:ℝ} (ha:-1<a) {n:ℕ} (hn:0<n) (z:ℂ) :
    Polynomial.aeval (z/(4*(n:ℂ))) (polynomial a n)=
      ∑'k,jacobi.Bessel.coefficient (a:ℂ) k*z^k*(correction n k:ℂ) := by
  -- No convergence restriction is imposed on z: the actual left series terminates.
  rw [tsum_eq_sum (s:=Finset.range (n+1)) (fun k hk=>by
    have hnK:n<k := by simpa only [Finset.mem_range,not_lt,Nat.add_one_le_iff] using hk
    rw [correction_terminates hn hnK,Complex.ofReal_zero,mul_zero])]
  simp only [polynomial,map_sum,map_mul,map_pow,aeval_C,aeval_X,Complex.coe_algebraMap]
  exact Finset.sum_congr rfl (fun k _=>scaled_coefficient ha hn k z)

/-- The single actual error series controlling the whole scaled Laguerre polynomial on a complex ball.
Use: scaling_error_limit and scaled_error_le give the full uniform Mehler--Heine theorem.
Article: jacobi, Proposition 6.1.
-/
def scalingError (a R:ℝ) (n:ℕ) : ℝ :=
  ∑'k,‖jacobi.Bessel.coefficient (a:ℂ) k‖*R^k*|correction n k-1|

/-- The actual uniform Laguerre error is summable at every positive finite degree.
Use: scaled_error_le subtracts genuine convergent series, rather than totalized infinite sums.
Article: jacobi, Proposition 6.1.
Proof: the error factor is at most one by correction_bounds, so the original entire Bessel norm series dominates it. -/
theorem scaling_error_summable (a:ℝ) {R:ℝ} (hR:0≤R) {n:ℕ} (hn:0<n) :
    Summable (fun k=>‖jacobi.Bessel.coefficient (a:ℂ) k‖*R^k*|correction n k-1|) := by
  apply (jacobi.Jacobi.bessel_majorant_summable (a:ℂ) hR).of_nonneg_of_le (fun k=>by positivity)
  intro k
  have hk:|correction n k-1|≤1 := by
    rw [abs_of_nonpos (by linarith [(correction_bounds hn k).2])]
    linarith [(correction_bounds hn k).1]
  exact mul_le_of_le_one_right (by positivity) hk

/-- The true common Laguerre error series tends to zero at every nonnegative complex radius.
Use: mehler_heine_uniform bounds every point of the ball by this same vanishing scalar.
Article: jacobi, Proposition 6.1.
Proof: every finite correction tends to one and its error is at
most one. Dominated convergence for series uses the genuine summable
Bessel coefficient norm series at the fixed radius. -/
theorem scaling_error_limit (a:ℝ) {R:ℝ} (hR:0≤R) :
    Tendsto (scalingError a R) atTop (𝓝 0) := by
  -- Domination is uniform over every coefficient index and every positive finite degree.
  have hh := tendsto_tsum_of_dominated_convergence (jacobi.Jacobi.bessel_majorant_summable (a:ℂ) hR)
    (f:=fun n k=>‖jacobi.Bessel.coefficient (a:ℂ) k‖*R^k*|correction n k-1|)
    (g:=fun _=>(0:ℝ)) (fun k=>by
      simpa only [sub_self,abs_zero,mul_zero] using
        (((correction_limit k).sub_const 1).abs).const_mul
          (‖jacobi.Bessel.coefficient (a:ℂ) k‖*R^k)) (by
      filter_upwards [eventually_gt_atTop (0:ℕ)] with n hn k
      rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
      have hk:|correction n k-1|≤1 := by
        rw [abs_of_nonpos (by linarith [(correction_bounds hn k).2])]
        linarith [(correction_bounds hn k).1]
      exact mul_le_of_le_one_right (by positivity) hk)
  change Tendsto (fun n=>∑'k,‖jacobi.Bessel.coefficient (a:ℂ) k‖*R^k*|correction n k-1|)
    atTop (𝓝 0)
  simpa only [tsum_zero] using hh

/-- The actual scaled classical Laguerre polynomial has the proved common norm error at every point of its complex ball.
Use: mehler_heine_uniform concerns the original finite polynomial throughout a complex neighborhood of every spectral zero.
Article: jacobi, Proposition 6.1.
Proof: subtract the genuine original Bessel series from the actual
corrected polynomial series. Its norm terms are bounded by the proved
summable error series, including the entire restored Bessel tail. -/
theorem scaled_error_le {a:ℝ} (ha:-1<a) {R:ℝ} (hR:0≤R) {n:ℕ} (hn:0<n)
    {z:ℂ} (hz:‖z‖≤R) :
    ‖Polynomial.aeval (z/(4*(n:ℂ))) (polynomial a n)- jacobi.Bessel.normalized (a:ℂ) z‖≤
      scalingError a R n := by
  -- Both summands are the actual source special functions, with their fixed normalizations.
  let f:=fun k=> jacobi.Bessel.coefficient (a:ℂ) k*z^k*((correction n k:ℂ)-1)
  have hsum:=scaling_error_summable a hR hn
  have hb (k:ℕ) : ‖f k‖≤‖jacobi.Bessel.coefficient (a:ℂ) k‖*R^k*|correction n k-1| := by
    dsimp only [f]
    rw [norm_mul,norm_mul,norm_pow,← Complex.ofReal_one,← Complex.ofReal_sub,
      Complex.norm_real,Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg z) hz k) (norm_nonneg _)) (abs_nonneg _)
  have hf:Summable f:=hsum.of_norm_bounded hb
  have hbase:=(jacobi.Bessel.normalized_hasSum (a:ℂ) z).summable
  have hcor:Summable (fun k=> jacobi.Bessel.coefficient (a:ℂ) k*z^k*(correction n k:ℂ)) := by
    convert hf.add hbase using 1
    funext k
    dsimp only [f]
    ring
  have he:Polynomial.aeval (z/(4*(n:ℂ))) (polynomial a n)- jacobi.Bessel.normalized (a:ℂ) z=∑'k,f k := by
    rw [normalized_scaled_eq_tsum ha hn,jacobi.Bessel.normalized_eq_tsum,← hcor.tsum_sub hbase]
    apply tsum_congr
    intro k
    dsimp only [f]
    ring
  rw [he]
  exact tsum_of_norm_bounded hsum.hasSum hb

/-- The original normalized Laguerre polynomials at z/(4*n) converge uniformly on every complex closed ball to the genuine normalized Bessel function.
Use: the ordered Laguerre edge limit in Proposition 6.1 starts from this fully proved complex Mehler--Heine theorem.
Article: jacobi, Proposition 6.1.
Source: DLMF 18.11.6.
Proof: the common actual error series tends to zero and bounds every
point of the complex ball. Its eventual epsilon bound is exactly the
uniform convergence criterion for the original polynomial family. -/
theorem mehler_heine_uniform {a:ℝ} (ha:-1<a) {R:ℝ} (hR:0≤R) :
    TendstoUniformlyOn (fun n:ℕ=>fun z:ℂ=>Polynomial.aeval (z/(4*(n:ℂ))) (polynomial a n))
      (jacobi.Bessel.normalized (a:ℂ)) atTop (Metric.closedBall 0 R) := by
  -- The same bound covers all complex points, not only positive real arguments.
  rw [Metric.tendstoUniformlyOn_iff]
  intro e he
  filter_upwards [(scaling_error_limit a hR).eventually (Iio_mem_nhds he),
    eventually_gt_atTop (0:ℕ)] with n hnerr hn z hz
  rw [dist_comm,dist_eq_norm]
  exact (scaled_error_le ha hR hn (by
    simpa only [Metric.mem_closedBall,dist_zero_right] using hz)).trans_lt hnerr

end
end jacobi.Laguerre
