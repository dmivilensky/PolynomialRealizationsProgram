import krylov.Correction.UniformBasisInverse

/-!
Article: main_krylov, thm:UCq, quantitative genuine terminal response geometry.
Use: Reuse the actual full-basis, oblique flag and measured-model algebra
in the uniform second-order RFC expansion without a smallest CG energy.
Source: proved genuine Gram conditioning, exact finite correction identities
and the existing weighted oblique response comparison.
-/

namespace krylov.Correction
noncomputable section
open Matrix krylov.Secant krylov.Stability
open scoped Matrix.Norms.L2Operator
variable {n : ℕ}

/-- The genuine inverse congruence of an actual full compressed operator is the original operator.
Use: Assemble the original actual uniform RFC cubic response.
Article: main_krylov, thm:UCq.
Proof: Cancel the two proved nonsingular actual basis factors without a norm or minimum-length assumption.
-/
theorem inverseCongruence_compressed (T E : Matrix (Fin n) (Fin n) ℝ) (hT : IsUnit T.det) :
    inverseCongruence T (Tᵀ*E*T)=E := by
  have ht : IsUnit Tᵀ.det := by simpa only [Matrix.det_transpose] using hT
  unfold inverseCongruence
  calc
    _ = (Tᵀ⁻¹*Tᵀ)*E*(T*T⁻¹) := by noncomm_ring
    _ = E := by rw [Matrix.nonsing_inv_mul _ ht,Matrix.mul_nonsing_inv _ hT,Matrix.one_mul,Matrix.mul_one]

/-- The actual primal full-basis Gram error is bounded by four times its true column Gram error.
Use: Assemble the original actual uniform RFC cubic response.
Article: main_krylov, thm:UCq.
Proof: The genuine inverse basis factors express the primal error as the actual column-error conjugate. Reuse the proved real column and inverse norms at most two.
-/
theorem full_column_primal_gram_error (T : Matrix (Fin n) (Fin n) ℝ)
    (hG : ‖Tᵀ*T-1‖≤(1/2 : ℝ)) : ‖T*Tᵀ-1‖≤4*‖Tᵀ*T-1‖ := by
  obtain ⟨hu,hT,hTi,_herr⟩ := full_column_inverse_transpose_bounds T hG
  rw [← Matrix.transpose_nonsing_inv,transpose_norm] at hTi
  have he : T*Tᵀ-1=T*(Tᵀ*T-1)*T⁻¹ := by
    calc
      _ = T*Tᵀ*(T*T⁻¹)-T*T⁻¹ := by rw [Matrix.mul_nonsing_inv _ hu,Matrix.mul_one]
      _ = _ := by noncomm_ring
  rw [he]
  calc
    _ ≤ (‖T‖*‖Tᵀ*T-1‖)*‖T⁻¹‖ := (norm_mul_le _ _).trans
      (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ (2*‖Tᵀ*T-1‖)*2 := by gcongr
    _ = _ := by ring

end
end krylov.Correction
