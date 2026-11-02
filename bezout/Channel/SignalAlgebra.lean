import bezout.Channel.SignalPermutation

/-!
Article: bezout, Appendix D, spectral-chart and root-order invariances.
Use: common interval-dependent physical scales cancel from literal signal gain
ratios, while temporal root permutations preserve both gain notions.
Proof: scalar multiplication of the actual Euclidean matrix map and finite
squared-entry sums, with all scales retained exactly.
-/

namespace bezout.Channel
noncomputable section
open scoped BigOperators
variable {N : ℕ} {J : Type*} [Fintype J]

/-- Scalar multiplication of a signal matrix is the same physical linear-map scaling. -/
theorem rectangularOperator_smul (M : Matrix J (Fin N) ℝ) (c : ℝ) :
    rectangularOperator (c • M)=c • rectangularOperator M := by
  apply ContinuousLinearMap.ext
  intro e
  ext j
  simp only [rectangularOperator_apply, smul_apply, PiLp.smul_apply,
    Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  ring

/-- The true signal operator norm scales by the absolute physical chart factor. -/
theorem rectangularNorm_smul (M : Matrix J (Fin N) ℝ) (c : ℝ) :
    rectangularNorm (c • M)=|c| *rectangularNorm M := by
  rw [rectangularNorm, rectangularOperator_smul, norm_smul, Real.norm_eq_abs]
  rfl

/-- Actual squared HS signal energy scales by the square of the physical chart factor. -/
theorem rectangularHsSq_smul (M : Matrix J (Fin N) ℝ) (c : ℝ) :
    rectangularHsSq (c • M)=c^2*rectangularHsSq M := by
  simp only [rectangularHsSq, Matrix.smul_apply, smul_eq_mul, mul_pow, Finset.mul_sum]

end
end bezout.Channel
