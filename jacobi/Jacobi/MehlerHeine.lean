import jacobi.Jacobi.BesselScaling

/-!
Article: jacobi, Proposition A.1.
The actual scaled Jacobi polynomials converge uniformly on every complex
closed ball to the actual normalized Bessel function in its squared
spectral variable. A common summable error series proves the uniformity.
Source: the classical dominated hypergeometric proof of Mehler--Heine.
Use: controls the entire Jacobi family and its error uniformly on a complex closed ball.
-/
namespace jacobi.Jacobi
noncomputable section
open Complex Real Set Polynomial Filter
open scoped Nat Topology
set_option backward.isDefEq.respectTransparency false

/-- The genuine Bessel coefficients give a summable scalar majorant at every nonnegative radius.
Use: controls the entire Jacobi family and its error uniformly on a complex closed ball.
Article: jacobi, Proposition A.1.
Proof: evaluate the already verified absolutely convergent Bessel
series at the nonnegative real radius and take its complex norms. -/
theorem bessel_majorant_summable (a : ℂ) {R : ℝ} (hR : 0≤R) :
    Summable (fun k => ‖jacobi.Bessel.coefficient a k‖*R^k) := by
  simpa only [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hR] using
    jacobi.Bessel.normalized_norm_summable a (R:ℂ)

/-- The actual correction error has the common exponential bound required by dominated convergence.
Use: bounds the entire finite-degree error, including the infinite Bessel tail after Jacobi termination.
Article: jacobi, Proposition A.1.
Proof: the correction norm is bounded by C^k and C>=1.
Triangle inequality gives norm(correction-1)<=C^k+1<=2*C^k. -/
theorem correction_error_bound (q : ℂ) {n : ℕ} (hn : 0<n) (k : ℕ) :
    ‖correction q n k-1‖≤2*(2*(2+‖q‖))^k := by
  have hC : (1:ℝ)≤2*(2+‖q‖) := by nlinarith [norm_nonneg q]
  have hpow : (1:ℝ)≤(2*(2+‖q‖))^k := one_le_pow₀ hC
  have h := norm_sub_le (correction q n k) (1:ℂ)
  rw [norm_one] at h
  linarith [correction_bound q hn k]

/-- The common scalar error controlling the scaled Jacobi series throughout a complex radius.
Use: its genuine limit zero gives compact uniform, rather than merely coefficientwise, convergence.
Article: jacobi, Proposition A.1.
-/
def scalingError (a q : ℂ) (R : ℝ) (n : ℕ) : ℝ :=
  ∑' k,‖jacobi.Bessel.coefficient a k‖*R^k*‖correction q n k-1‖

/-- The scalar majorant for the Jacobi-to-Bessel error is summable at every positive finite degree.
Use: legitimizes every infinite-sum subtraction and the uniform norm estimate.
Article: jacobi, Proposition A.1.
Proof: the correction error is bounded by 2*C^k, so the series is
dominated by twice the genuine Bessel norm series at radius C*R. -/
theorem scaling_error_summable (a q : ℂ) {R : ℝ} (hR : 0≤R) {n : ℕ} (hn : 0<n) :
    Summable (fun k => ‖jacobi.Bessel.coefficient a k‖*R^k*‖correction q n k-1‖) := by
  -- The same bound handles all degrees beyond the terminating Jacobi degree.
  have hsum := (bessel_majorant_summable a (R := 2*(2+‖q‖)*R) (by positivity)).mul_left 2
  apply Summable.of_nonneg_of_le (fun k => by positivity) _ hsum
  intro k
  have h := mul_le_mul_of_nonneg_left (correction_error_bound q hn k)
    (show 0≤‖jacobi.Bessel.coefficient a k‖*R^k by positivity)
  convert h using 1
  rw [mul_pow]
  ring

/-- The actual common Jacobi-to-Bessel error tends to zero at every complex radius.
Use: the limit is independent of the point in the ball and therefore proves true uniform convergence.
Article: jacobi, Proposition A.1.
Proof: each finite correction tends to one. The actual error
coefficients therefore tend to zero and share twice the summable Bessel
majorant at radius C*R. Apply the proved dominated convergence theorem for series. -/
theorem scaling_error_limit (a q : ℂ) {R : ℝ} (hR : 0≤R) :
    Tendsto (scalingError a q R) atTop (𝓝 0) := by
  -- The summable bound is uniform in every positive finite Jacobi degree.
  have hsum := (bessel_majorant_summable a (R := 2*(2+‖q‖)*R) (by positivity)).mul_left 2
  have h := tendsto_tsum_of_dominated_convergence hsum
    (f := fun n k => ‖jacobi.Bessel.coefficient a k‖*R^k*‖correction q n k-1‖)
    (g := fun _ => (0:ℝ))
    (fun k => by
      have hk := ((correction_limit q k).sub_const 1).norm.const_mul
        (‖jacobi.Bessel.coefficient a k‖*R^k)
      simpa only [sub_self,norm_zero,mul_zero] using hk)
    (by
      filter_upwards [eventually_gt_atTop (0:ℕ)] with n hn
      intro k
      rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
      have hh := mul_le_mul_of_nonneg_left (correction_error_bound q hn k)
        (show 0≤‖jacobi.Bessel.coefficient a k‖*R^k by positivity)
      convert hh using 1
      rw [mul_pow]
      ring)
  change Tendsto (fun n => ∑' k,‖jacobi.Bessel.coefficient a k‖*R^k*‖correction q n k-1‖)
    atTop (𝓝 0)
  simpa only [tsum_zero] using h

/-- The common actual error series bounds the original finite Jacobi-to-Bessel difference at every point of its complex ball.
Use: upgrades the genuine convergent series limit to the compact uniform Mehler--Heine theorem.
Article: jacobi, Proposition A.1.
Proof: subtract the genuine Bessel series from the exact corrected
Jacobi series. The difference series is summable under the proved error
majorant. Bound each term using norm(z)<=R, then apply the norm bound
for the actual convergent sum. -/
theorem scaled_error_le {a b : ℂ} (ha : -1<a.re) {R : ℝ} (hR : 0≤R)
    {n : ℕ} (hn : 0<n) {z : ℂ} (hz : ‖z‖≤R) :
    ‖normalized a b n (1-z/(2*(n:ℂ)^2))- jacobi.Bessel.normalized a z‖≤
      scalingError a (a+b+1) R n := by
  -- All series here sum to their original defined special functions.
  let f := fun k => jacobi.Bessel.coefficient a k*z^k*(correction (a+b+1) n k-1)
  have hsum := scaling_error_summable a (a+b+1) hR hn
  have hbound (k : ℕ) :
      ‖f k‖≤‖jacobi.Bessel.coefficient a k‖*R^k*‖correction (a+b+1) n k-1‖ := by
    dsimp only [f]
    rw [norm_mul,norm_mul,norm_pow]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg z) hz k) (norm_nonneg _)) (norm_nonneg _)
  have hf : Summable f := hsum.of_norm_bounded hbound
  have hbase := (jacobi.Bessel.normalized_hasSum a z).summable
  have hcor : Summable (fun k => jacobi.Bessel.coefficient a k*z^k*correction (a+b+1) n k) := by
    convert hf.add hbase using 1
    funext k
    dsimp only [f]
    ring
  have he : normalized a b n (1-z/(2*(n:ℂ)^2))- jacobi.Bessel.normalized a z=∑' k,f k := by
    rw [normalized_scaled_eq_tsum ha hn,jacobi.Bessel.normalized_eq_tsum,← hcor.tsum_sub hbase]
    apply tsum_congr
    intro k
    dsimp only [f]
    ring
  rw [he]
  exact tsum_of_norm_bounded hsum.hasSum hbound

/-- The actual squared-edge Jacobi scaling converges uniformly on every complex closed ball to the genuine normalized Bessel function.
Use: the compact uniform Mehler--Heine limit underlying the finite-edge zero and spectral convergence theorems.
Article: jacobi, Proposition A.1.
Proof: a single genuine summable error series bounds every point of
the ball and tends to zero. Its eventual epsilon bound, together with
the exact actual-series comparison, is the uniform convergence criterion. -/
theorem mehler_heine_uniform {a b : ℂ} (ha : -1<a.re) {R : ℝ} (hR : 0≤R) :
    TendstoUniformlyOn (fun n : ℕ => fun z : ℂ => normalized a b n (1-z/(2*(n:ℂ)^2)))
      (jacobi.Bessel.normalized a) atTop (Metric.closedBall 0 R) := by
  -- The uniform statement covers the whole complex ball, not only real arguments or fixed coefficients.
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [(scaling_error_limit a (a+b+1) hR).eventually (Iio_mem_nhds hε),
    eventually_gt_atTop (0:ℕ)] with n hnerr hn
  intro z hz
  rw [dist_comm,dist_eq_norm]
  exact (scaled_error_le ha hR hn (by
    simpa only [Metric.mem_closedBall,dist_zero_right] using hz)).trans_lt hnerr

end
end jacobi.Jacobi
