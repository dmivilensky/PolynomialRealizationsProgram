import krylov.Stability.UniformFlagBounds

/-!
Article: main_krylov, thm:UCq, true normalized terminal basis reconstruction.
Use: Derive actual full column and inverse-transpose bounds and their linear
difference from the genuine near-identity direction/recorded-column Gram.
Source: proved real C-star Gram identities, Neumann inverse estimates and
exact nonsingular matrix multiplication; no individual column-length bound.
-/

namespace krylov.Correction
noncomputable section
open Matrix krylov.Stability
open scoped Matrix.Norms.L2Operator
variable {n : ℕ}

/-- A genuine full normalized column matrix with half-identity Gram has derived inverse domain, bounded column and inverse-transpose norms, and twice-Gram-error inverse-transpose displacement.
Use: Quantify the true terminal reconstruction error in the uniform RFC cubic response.
Article: main_krylov, thm:UCq.
Proof: Reuse actual Gram and inverse-Gram C-star norm identities to bound both real operator factors. Their genuine nonsingular inverse identity writes the inverse-transpose displacement as its actual inverse-transpose times the Gram error.
-/
theorem full_column_inverse_transpose_bounds (T : Matrix (Fin n) (Fin n) ℝ)
    (hG : ‖Tᵀ*T-1‖≤(1/2 : ℝ)) :
    IsUnit T.det ∧ ‖T‖≤2 ∧ ‖Tᵀ⁻¹‖≤2 ∧ ‖Tᵀ⁻¹-T‖≤2*‖Tᵀ*T-1‖ := by
  have hu := column_unit_of_near_gram T hG
  have hnorm := gram_norm_bound T hG
  have hT : ‖T‖≤2 := by nlinarith [norm_nonneg T]
  have hInvGram := (near_identity_inverse (Tᵀ*T) hG).2.1
  have he : ‖(Tᵀ*T)⁻¹‖=‖T⁻¹‖*‖T⁻¹‖ := by
    rw [Matrix.mul_inv_rev,← Matrix.transpose_nonsing_inv]
    simpa only [Matrix.star_eq_conjTranspose,Matrix.conjTranspose_eq_transpose_of_trivial] using
      (CStarRing.norm_self_mul_star (x := T⁻¹))
  rw [he] at hInvGram
  have hTi : ‖Tᵀ⁻¹‖≤2 := by
    rw [← Matrix.transpose_nonsing_inv,transpose_norm]
    nlinarith [norm_nonneg T⁻¹]
  have htranspose : IsUnit Tᵀ.det := by simpa only [Matrix.det_transpose] using hu
  have hsplit : Tᵀ⁻¹-T=Tᵀ⁻¹*(1-Tᵀ*T) := by
    rw [mul_sub,Matrix.mul_one,← Matrix.mul_assoc,Matrix.nonsing_inv_mul _ htranspose,Matrix.one_mul]
  refine ⟨hu,hT,hTi,?_⟩
  rw [hsplit]
  apply (norm_mul_le _ _).trans
  rw [norm_sub_rev]
  exact mul_le_mul_of_nonneg_right hTi (norm_nonneg _)

end
end krylov.Correction
