import krylov.LinearAlgebra.SchurDeterminant
import krylov.Realization.RawContinuation
import Mathlib.Logic.Equiv.Fin.Basic

set_option autoImplicit false
/-!
Article: main_krylov, prop:phi(a), actual prefix Schur complement.
Use: split the original physical finite matrix into its genuine leading and trailing indices and construct its true positive Schur complement.
Source: the standard Schur-complement positivity theorem applied to the actual reindexed positive matrix.
-/

namespace krylov.Envelope
noncomputable section
open krylov.Realization krylov.LinearAlgebra Matrix
variable {N : ℕ}

/-- The genuine chronological leading and trailing index equivalence.
Use: The genuine chronological leading and trailing index equivalence.
Article: main_krylov, prop:phi(a), actual prefix Schur complement.
Proof: Compose the standard finite-sum equivalence with the exact prefix-length identity. -/
def rawSplitEquiv (N j : ℕ) (hj : j≤N) : (Fin j ⊕ Fin (N-j)) ≃ Fin N :=
  finSumFinEquiv.trans (finCongr (Nat.add_sub_of_le hj))

/-- A genuine leading split index retains its original chronological value.
Use: A genuine leading split index retains its original chronological value.
Article: main_krylov, prop:phi(a), actual prefix Schur complement.
Proof: Compute the actual finite-sum equivalence. -/
theorem rawSplitEquiv_left (N j : ℕ) (hj : j≤N) (i : Fin j) :
    (rawSplitEquiv N j hj (Sum.inl i)).val=i.val := by
  simp only [rawSplitEquiv,Equiv.trans_apply,finSumFinEquiv_apply_left,finCongr_apply,Fin.val_cast,Fin.val_castAdd]

/-- A genuine trailing split index has the true prefix offset.
Use: A genuine trailing split index has the true prefix offset.
Article: main_krylov, prop:phi(a), actual prefix Schur complement.
Proof: Compute the actual finite-sum equivalence. -/
theorem rawSplitEquiv_right (N j : ℕ) (hj : j≤N) (i : Fin (N-j)) :
    (rawSplitEquiv N j hj (Sum.inr i)).val=j+i.val := by
  simp only [rawSplitEquiv,Equiv.trans_apply,finSumFinEquiv_apply_right,finCongr_apply,Fin.val_cast,Fin.val_natAdd]

/-- The actual Schur complement of the true leading principal block.
Use: The actual Schur complement of the true leading principal block.
Article: main_krylov, prop:phi(a), actual prefix Schur complement.
Proof: Use the original physical matrix blocks and its genuine nonsingular leading inverse. -/
def rawSchurComplement (T : Matrix (Fin N) (Fin N) ℝ) (j : ℕ) (hj : j≤N) : Matrix (Fin (N-j)) (Fin (N-j)) ℝ :=
  let M := T.submatrix (rawSplitEquiv N j hj) (rawSplitEquiv N j hj)
  M.toBlocks₂₂-M.toBlocks₂₁*M.toBlocks₁₁⁻¹*M.toBlocks₁₂

/-- The actual split leading block is exactly the true contiguous prefix.
Use: The actual split leading block is exactly the true contiguous prefix.
Article: main_krylov, prop:phi(a), actual prefix Schur complement.
Proof: Compare the actual matrix entries at their original leading indices. -/
theorem rawSplit_leading (T : Matrix (Fin N) (Fin N) ℝ) (j : ℕ) (hj : j≤N) :
    (T.submatrix (rawSplitEquiv N j hj) (rawSplitEquiv N j hj)).toBlocks₁₁=rawBlock T 0 j (by omega) := by
  ext i l
  change T _ _=T _ _
  congr 1 <;> apply Fin.ext <;> simp only [rawSplitEquiv_left,Nat.zero_add]

/-- The actual split trailing block is exactly the true contiguous suffix.
Use: The actual split trailing block is exactly the true contiguous suffix.
Article: main_krylov, prop:phi(a), actual prefix Schur complement.
Proof: Read the actual offset finite indices. -/
theorem rawSplit_trailing (T : Matrix (Fin N) (Fin N) ℝ) (j : ℕ) (hj : j≤N) :
    (T.submatrix (rawSplitEquiv N j hj) (rawSplitEquiv N j hj)).toBlocks₂₂=rawBlock T j (N-j) (by omega) := by
  ext i l
  change T _ _=T _ _
  rfl

/-- Every actual prefix Schur complement of a positive definite matrix is positive definite, including empty boundaries.
Use: Every actual prefix Schur complement of a positive definite matrix is positive definite, including empty boundaries.
Article: main_krylov, prop:phi(a), actual prefix Schur complement.
Proof: Reindex the actual positive quadratic form and apply the genuine block Schur positivity theorem. -/
theorem rawSchurComplement_posDef (T : Matrix (Fin N) (Fin N) ℝ) (hT : T.PosDef) (j : ℕ) (hj : j≤N) :
    (rawSchurComplement T j hj).PosDef := by
  let M := T.submatrix (rawSplitEquiv N j hj) (rawSplitEquiv N j hj)
  have hm : M.PosDef := hT.submatrix (rawSplitEquiv N j hj).injective
  have he : M=Matrix.fromBlocks M.toBlocks₁₁ M.toBlocks₁₂ M.toBlocks₂₁ M.toBlocks₂₂ := by
    ext i l
    cases i <;> cases l <;> rfl
  rw [he] at hm
  exact block_schur_posDef _ _ _ _ hm
end
end krylov.Envelope
