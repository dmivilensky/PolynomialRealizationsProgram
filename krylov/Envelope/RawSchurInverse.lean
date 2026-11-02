import krylov.Envelope.RawSchur
set_option autoImplicit false
/-!
Article: main_krylov, prop:phi(a), actual Schur inverse principal block.
Use: transfer genuine finite spectral interval bounds from the original matrix to its true Schur complement.
Source: standard true Schur inverse-block formula and actual inverse equivariance under the chronological finite split.
-/

namespace krylov.Envelope
noncomputable section
open krylov.Realization krylov.LinearAlgebra Matrix
variable {N : ℕ}

/-- The inverse of the actual prefix Schur complement is exactly the true contiguous suffix of the original inverse.
Use: The inverse of the actual prefix Schur complement is exactly the true contiguous suffix of the original inverse.
Article: main_krylov, prop:phi(a), actual Schur inverse principal block.
Proof: Derive the real leading, Schur and whole inverse domains from positivity, apply the actual block inverse formula and undo the genuine reindexing. -/
theorem rawSchur_inverse (T : Matrix (Fin N) (Fin N) ℝ) (hT : T.PosDef)
    (j : ℕ) (hj : j≤N) :
    (rawSchurComplement T j hj)⁻¹=rawBlock T⁻¹ j (N-j) (by omega) := by
  -- The true inverse-block theorem is applied only after all actual positive determinant domains are established.
  let e := rawSplitEquiv N j hj
  let M := T.submatrix e e
  have hm : M.PosDef := hT.submatrix e.injective
  have hA : IsUnit M.toBlocks₁₁.det := isUnit_iff_ne_zero.mpr (hm.submatrix Sum.inl_injective).det_pos.ne'
  have hS : IsUnit (M.toBlocks₂₂-M.toBlocks₂₁*M.toBlocks₁₁⁻¹*M.toBlocks₁₂).det :=
    isUnit_iff_ne_zero.mpr (rawSchurComplement_posDef T hT j hj).det_pos.ne'
  have hTd : IsUnit (Matrix.fromBlocks M.toBlocks₁₁ M.toBlocks₁₂ M.toBlocks₂₁ M.toBlocks₂₂).det := by
    rw [Matrix.fromBlocks_toBlocks]
    exact isUnit_iff_ne_zero.mpr hm.det_pos.ne'
  -- Reindex the actual whole inverse back to its original physical suffix entries.
  have h := block_schur_inverse M.toBlocks₁₁ M.toBlocks₁₂ M.toBlocks₂₁ M.toBlocks₂₂ hA hS hTd
  rw [Matrix.fromBlocks_toBlocks] at h
  change (M⁻¹).submatrix Sum.inr Sum.inr=(rawSchurComplement T j hj)⁻¹ at h
  rw [← h]
  dsimp only [M]
  rw [Matrix.inv_submatrix_equiv]
  rfl
end
end krylov.Envelope
