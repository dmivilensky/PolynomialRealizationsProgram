import jacobi.Comparison.CholeskyBounds
import jacobi.Comparison.WeightError
import jacobi.Support.WeightedSegments

/-!
Article: jacobi, Theorem 2.1.
The original support probabilities and segment estimates transfer to
the true target probabilities at every original spectral index. Exact
Schur rows then give the uniform target-polynomial bound on the full
physical half chain, with the actual positive normalizations.
Use: targetPolynomial_weighted_bound inserts this genuine support bound into the actual Schur row formula, uniformly over the entire spectrum.
-/
namespace jacobi.Comparison
noncomputable section
open Real Set Filter Polynomial jacobi.Support jacobi.Finite
open scoped Topology

/-- The actual target probabilities give a common scaled bound on the
original support polynomials at every actual target spectral node.
Use: targetPolynomial_weighted_bound inserts this genuine support bound
into the actual Schur row formula, uniformly over the entire spectrum.
Article: jacobi, Theorem 2.1.
Proof: apply the complete original support-weighted segment bound at
the actual target endpoint. The proved positive probability comparison
and monotonicity of the square root replace support by target weights. -/
theorem supportPolynomial_targetWeighted_bound {a b:ℝ} (ha:-1<a) (hb:-1<b) :
    ∃ A:ℝ, 0<A ∧ ∀ᶠ n:ℕ in atTop, ∀ i:Fin (n+1), 2*i.val≤n+1 →
      ∀ k:Fin (n+1), sqrt (((n:ℝ)+1)*(targetMeasure a b ha hb n).weight k)*
        |(supportPolynomial a b ha hb n i).eval ((jacobi.Jacobi.nodes a b ha hb (n+1)).value k)|≤A := by
  -- At the actual target endpoint, compare the genuine positive spectral probabilities.
  obtain ⟨C,hC,hbound⟩ := supportPolynomial_segment_bounds ha hb
  obtain ⟨d,D,_,hD,hweight⟩ := comparisonWeight_bounds ha hb
  refine ⟨sqrt D*C,by positivity,?_⟩
  filter_upwards [hbound,hweight] with n hn hw
  intro i hi k
  have hval := (hn i hi k _ (right_mem_uIcc)).1
  have hprob : (targetMeasure a b ha hb n).weight k≤D*(supportMeasure a b ha hb n).weight k :=
    (div_le_iff₀ ((supportMeasure a b ha hb n).positive k)).mp (hw k).2
  have hs := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hprob
    (by positivity : (0:ℝ)≤(n:ℝ)+1))
  have hmul : ((n:ℝ)+1)*(D*(supportMeasure a b ha hb n).weight k)=
      D*(((n:ℝ)+1)*(supportMeasure a b ha hb n).weight k) := by ring
  rw [hmul,Real.sqrt_mul hD.le] at hs
  calc
    _ ≤ (sqrt D*sqrt (((n:ℝ)+1)*(supportMeasure a b ha hb n).weight k))*
        |(supportPolynomial a b ha hb n i).eval ((jacobi.Jacobi.nodes a b ha hb (n+1)).value k)| :=
      mul_le_mul_of_nonneg_right hs (abs_nonneg _)
    _ ≤ sqrt D*C := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left hval (sqrt_nonneg D)

/-- The genuine original positive Schur square roots have uniformly
bounded reciprocals on the physical half chain.
Use: targetPolynomial_weighted_bound controls the actual normalization
in the exact source target polynomial formula.
Article: jacobi, Theorem 2.1.
Proof: the actual uniform O(1/N) error is eventually at most one half.
The original positive square root is consequently at least one half,
so its genuine reciprocal is at most two. -/
theorem rowNormalization_inverse_sqrt_bound {a b:ℝ} (ha:-1<a) (hb:-1<b) :
    ∀ᶠ n:ℕ in atTop, ∀ i:Fin (n+1), 2*i.val≤n+1 →
      (sqrt (rowNormalization a b ha hb n i))⁻¹≤2 := by
  -- The proved uniform O(1/N) error keeps the actual positive square root away from zero.
  obtain ⟨K,_,hbound⟩ := cholesky_uniform_bounds ha hb
  have hlim : Tendsto (fun n:ℕ => K/((n:ℝ)+1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      (tendsto_atTop_add_const_right atTop (1:ℝ) tendsto_natCast_atTop_atTop)
  filter_upwards [hbound,hlim.eventually (Iio_mem_nhds (by norm_num : (0:ℝ)<1/2))] with n hn hsmall
  intro i hi
  have herr : |rowNormalization a b ha hb n i-1|≤K/((n:ℝ)+1) :=
    (le_div_iff₀ (by positivity : (0:ℝ)<(n:ℝ)+1)).mpr (by nlinarith [(hn i hi).2.2])
  have hq : (1/4:ℝ)≤rowNormalization a b ha hb n i := by linarith [(abs_le.mp herr).1]
  have hs : (1/2:ℝ)≤sqrt (rowNormalization a b ha hb n i) := by
    have hh := Real.sqrt_le_sqrt hq
    norm_num at hh ⊢
    exact hh
  rw [inv_eq_one_div]
  apply (div_le_iff₀ (sqrt_pos.mpr (rowNormalization_pos a b ha hb n i))).mpr
  linarith

/-- The true target polynomials, with their actual target probabilities,
have one original matrix-size-scaled bound over all spectral indices
and every physical half-chain coordinate.
Use: target_eigenvector_uniform_bounds converts this actual polynomial
bound into the original full finite eigenvector estimate.
Article: jacobi, Appendix C.4 (uniform eigenvector limits).
Proof: evaluate the genuine target/support Schur row identity at the
actual target node. The preceding support polynomials obey the same
uniform target-weighted bound. The actual row has bounded absolute
coefficient mass and a bounded inverse positive normalization, yielding
one original constant for the entire growing spectral array. -/
theorem targetPolynomial_weighted_bound {a b:ℝ} (ha:-1<a) (hb:-1<b) :
    ∃ C:ℝ, 0<C ∧ ∀ᶠ n:ℕ in atTop, ∀ i:Fin (n+1), 2*i.val≤n+1 →
      ∀ k:Fin (n+1), sqrt (((n:ℝ)+1)*(targetMeasure a b ha hb n).weight k)*
        |(targetPolynomial a b ha hb n i).eval ((jacobi.Jacobi.nodes a b ha hb (n+1)).value k)|≤C := by
  -- The same weighted support bound controls the full actual preceding-row polynomial sum.
  obtain ⟨A,hA,hbound⟩ := supportPolynomial_targetWeighted_bound ha hb
  obtain ⟨K,hK,hrows⟩ := cholesky_uniform_bounds ha hb
  refine ⟨2*(A*(1+K)),by positivity,?_⟩
  filter_upwards [hbound,hrows,rowNormalization_inverse_sqrt_bound ha hb] with n hn hr hq
  intro i hi k
  let W := sqrt (((n:ℝ)+1)*(targetMeasure a b ha hb n).weight k)
  let x := (jacobi.Jacobi.nodes a b ha hb (n+1)).value k
  let P := fun j:Fin (n+1) => (supportPolynomial a b ha hb n j).eval x
  let c := rowCoefficient a b ha hb n i
  have hP (j:Fin i.val) : W*|P (Gram.before i j)|≤A := by
    apply hn
    have hj := j.isLt
    change 2*j.val≤n+1
    omega
  -- Every preceding original polynomial has the same spectral-weighted bound.
  have hsum : W*|∑ j:Fin i.val, c j*P (Gram.before i j)|≤A*K := by
    calc
      _ ≤ W*∑ j:Fin i.val, |c j*P (Gram.before i j)| :=
        mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (sqrt_nonneg _)
      _ = ∑ j:Fin i.val, |c j| * (W*|P (Gram.before i j)|) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        rw [abs_mul]
        ring
      _ ≤ ∑ j:Fin i.val, A*|c j| := Finset.sum_le_sum (fun j _ => by
        have hh := mul_le_mul_of_nonneg_left (hP j) (abs_nonneg (c j))
        simpa only [mul_comm A] using hh)
      _ ≤ A*K := by rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left (hr i hi).1 hA.le
  have htotal : W*|P i+∑ j:Fin i.val, c j*P (Gram.before i j)|≤A*(1+K) := by
    calc
      _ ≤ W*(|P i|+|∑ j:Fin i.val, c j*P (Gram.before i j)|) :=
        mul_le_mul_of_nonneg_left (abs_add_le _ _) (sqrt_nonneg _)
      _ ≤ A+A*K := by rw [mul_add]; exact add_le_add (hn i hi k) hsum
      _ = _ := by ring
  -- Insert the exact target/support Schur formula only after bounding its full actual row.
  rw [targetPolynomial_schur]
  simp only [Polynomial.eval_smul,smul_eq_mul,Polynomial.eval_add,Polynomial.eval_finsetSum,
    abs_mul,abs_of_pos (inv_pos.mpr (sqrt_pos.mpr (rowNormalization_pos a b ha hb n i)))]
  change W*((sqrt (rowNormalization a b ha hb n i))⁻¹*|P i+∑ j:Fin i.val, c j*P (Gram.before i j)|)≤_
  rw [mul_left_comm W]
  exact (mul_le_mul_of_nonneg_left htotal
    (inv_nonneg.mpr (sqrt_nonneg _))).trans
    (mul_le_mul_of_nonneg_right (hq i hi) (by positivity))

end
end jacobi.Comparison
