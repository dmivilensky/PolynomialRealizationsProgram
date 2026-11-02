import krylov.Envelope.RawSchur
set_option autoImplicit false
/-!
Article: main_krylov, prop:phi(a), genuine trailing-shift Schur determinant.
Use: identify the actual original matrix suffix shift with the true trailing block pencil and its inverse-normalized Schur determinant.
Source: actual chronological split indices, true positive principal blocks and the standard nonsingular Schur determinant factorization.
-/

namespace krylov.Envelope
noncomputable section
open krylov.Realization krylov.LinearAlgebra Matrix
variable {N : ℕ}

/-- The original physical suffix shift changes exactly the actual trailing split block.
Use: The original physical suffix shift changes exactly the actual trailing split block.
Article: main_krylov, prop:phi(a), genuine trailing-shift Schur determinant.
Proof: Inspect all four genuine leading and trailing index combinations; the actual diagonal shift vanishes across the blocks. -/
theorem rawSuffixShift_split (T : Matrix (Fin N) (Fin N) ℝ) (j : ℕ) (hj : j≤N) (lam : ℝ) :
    (rawSuffixShift T j lam).submatrix (rawSplitEquiv N j hj) (rawSplitEquiv N j hj)=
    let M := T.submatrix (rawSplitEquiv N j hj) (rawSplitEquiv N j hj)
    Matrix.fromBlocks M.toBlocks₁₁ M.toBlocks₁₂ M.toBlocks₂₁ (M.toBlocks₂₂-lam • 1) := by
  -- The real split equivalence identifies exactly which physical diagonal entries are shifted.
  ext a b
  cases a with
  | inl a =>
    cases b with
    | inl b =>
      simp [rawSuffixShift,Matrix.diagonal_apply,rawSplitEquiv_left,show ¬ j≤a.val by omega]
      rfl
    | inr b =>
      simp [rawSuffixShift,(rawSplitEquiv N j hj).injective.eq_iff]
      rfl
  | inr a =>
    cases b with
    | inl b =>
      simp [rawSuffixShift,(rawSplitEquiv N j hj).injective.eq_iff]
      rfl
    | inr b =>
      simp [rawSuffixShift,Matrix.diagonal_apply,Matrix.one_apply,
        (rawSplitEquiv N j hj).injective.eq_iff,rawSplitEquiv_right]
      rfl

/-- The original physical suffix-shift determinant ratio is the genuine inverse-normalized actual Schur determinant.
Use: The original physical suffix-shift determinant ratio is the genuine inverse-normalized actual Schur determinant.
Article: main_krylov, prop:phi(a), genuine trailing-shift Schur determinant.
Proof: Derive both genuine nonsingular block domains from positivity, reindex the actual determinants and apply the true block factorization. -/
theorem raw_schur_shift_ratio (T : Matrix (Fin N) (Fin N) ℝ) (hT : T.PosDef)
    (j : ℕ) (hj : j≤N) (lam : ℝ) :
    (rawSuffixShift T j lam).det/T.det=(1-lam • (rawSchurComplement T j hj)⁻¹).det := by
  -- Positivity supplies the actual inverse domains before either genuine determinant is canceled.
  let e := rawSplitEquiv N j hj
  let M := T.submatrix e e
  have hm : M.PosDef := hT.submatrix e.injective
  have hA : IsUnit M.toBlocks₁₁.det := isUnit_iff_ne_zero.mpr (hm.submatrix Sum.inl_injective).det_pos.ne'
  have hS : IsUnit (M.toBlocks₂₂-M.toBlocks₂₁*M.toBlocks₁₁⁻¹*M.toBlocks₁₂).det :=
    isUnit_iff_ne_zero.mpr (rawSchurComplement_posDef T hT j hj).det_pos.ne'
  have h := block_schur_shift_ratio M.toBlocks₁₁ M.toBlocks₁₂ M.toBlocks₂₁ M.toBlocks₂₂ hA hS lam
  rw [Matrix.fromBlocks_toBlocks] at h
  rw [← Matrix.det_submatrix_equiv_self e (rawSuffixShift T j lam),← Matrix.det_submatrix_equiv_self e T,
    rawSuffixShift_split]
  exact h
end
end krylov.Envelope
