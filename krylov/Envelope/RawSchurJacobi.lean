import krylov.Envelope.RawSchur
import krylov.Realization.RawCG
set_option autoImplicit false
/-!
Article: main_krylov, prop:phi(a), genuine Schur Jacobi structure and simple spectrum.
Use: establish actual simple continuation zeros from the original physical matrix without assuming eigenvalue separation.
Source: the true tridiagonal cross block changes only the first suffix diagonal; reuse actual full first-site CG activity and the genuine spectral atom cardinality theorem.
-/

namespace krylov.Envelope
noncomputable section
open krylov.Reference krylov.Realization Matrix
variable {N : ℕ}

/-- Every actual Schur off-diagonal entry is exactly its original physical suffix entry.
Use: Every actual Schur off-diagonal entry is exactly its original physical suffix entry.
Article: main_krylov, prop:phi(a), genuine Schur Jacobi structure and simple spectrum.
Proof: Tridiagonality annihilates the real cross-block row or column whenever the corresponding suffix index is positive. -/
theorem rawSchur_off_diagonal (T : Matrix (Fin N) (Fin N) ℝ)
    (htri : ∀ i l : Fin N,i.val+1 < l.val ∨ l.val+1 < i.val → T i l=0)
    (j : ℕ) (hj : j≤N) (i l : Fin (N-j)) (hil : i≠l) :
    rawSchurComplement T j hj i l=rawBlock T j (N-j) (by omega) i l := by
  -- The genuine cross block is supported only at the first suffix site; every other row or column vanishes.
  let M := T.submatrix (rawSplitEquiv N j hj) (rawSplitEquiv N j hj)
  have hz : (M.toBlocks₂₁*M.toBlocks₁₁⁻¹*M.toBlocks₁₂) i l=0 := by
    by_cases hi : 0 < i.val
    · have hc (a : Fin j) : M.toBlocks₂₁ i a=0 := by
        apply htri
        right
        change a.val+1 < j+i.val
        omega
      simp only [Matrix.mul_apply,hc,zero_mul,Finset.sum_const_zero]
    · have hl : 0 < l.val := by
        have he : i.val≠l.val := fun h => hil (Fin.ext h)
        omega
      have hb (a : Fin j) : M.toBlocks₁₂ a l=0 := by
        apply htri
        left
        change a.val+1 < j+l.val
        omega
      simp only [Matrix.mul_apply,hb,mul_zero,Finset.sum_const_zero]
  -- Therefore the actual Schur correction cannot change any true off-diagonal entry.
  change M.toBlocks₂₂ i l-(M.toBlocks₂₁*M.toBlocks₁₁⁻¹*M.toBlocks₁₂) i l=_
  rw [hz,sub_zero]
  rfl

/-- The genuine prefix Schur complement retains actual tridiagonality.
Use: The genuine prefix Schur complement retains actual tridiagonality.
Article: main_krylov, prop:phi(a), genuine Schur Jacobi structure and simple spectrum.
Proof: Its true off-diagonal entries agree with the original matrix. -/
theorem rawSchur_tridiagonal (T : Matrix (Fin N) (Fin N) ℝ)
    (htri : ∀ i l : Fin N,i.val+1 < l.val ∨ l.val+1 < i.val → T i l=0)
    (j : ℕ) (hj : j≤N) :
    ∀ i l : Fin (N-j),i.val+1 < l.val ∨ l.val+1 < i.val → rawSchurComplement T j hj i l=0 := by
  intro i l hil
  rw [rawSchur_off_diagonal T htri j hj i l (by intro h;subst l;omega)]
  apply htri
  change j+i.val+1 < j+l.val ∨ j+l.val+1 < j+i.val
  omega

/-- Every actual Schur adjacent edge retains its genuine strict negative sign.
Use: Every actual Schur adjacent edge retains its genuine strict negative sign.
Article: main_krylov, prop:phi(a), genuine Schur Jacobi structure and simple spectrum.
Proof: Read the original internal suffix edge through the true off-diagonal identity. -/
theorem rawSchur_adjacent_neg (T : Matrix (Fin N) (Fin N) ℝ)
    (htri : ∀ i l : Fin N,i.val+1 < l.val ∨ l.val+1 < i.val → T i l=0)
    (hneg : ∀ i l : Fin N,i.val+1=l.val → T i l < 0)
    (j : ℕ) (hj : j≤N) :
    ∀ i l : Fin (N-j),i.val+1=l.val → rawSchurComplement T j hj i l < 0 := by
  intro i l hil
  rw [rawSchur_off_diagonal T htri j hj i l (by intro h;subst l;omega)]
  apply hneg
  change j+i.val+1=j+l.val
  omega

/-- The actual positive prefix Schur complement has genuinely distinct real eigenvalues.
Use: The actual positive prefix Schur complement has genuinely distinct real eigenvalues.
Article: main_krylov, prop:phi(a), genuine Schur Jacobi structure and simple spectrum.
Proof: Its actual first-site CG run has full activity by the proved physical Jacobi theorem; full true atom count forces distinct eigenvalues. -/
theorem rawSchur_simple_spectrum (T : Matrix (Fin N) (Fin N) ℝ) (hT : T.PosDef)
    (htri : ∀ i l : Fin N,i.val+1 < l.val ∨ l.val+1 < i.val → T i l=0)
    (hneg : ∀ i l : Fin N,i.val+1=l.val → T i l < 0)
    (j : ℕ) (hj : j≤N) :
    Function.Injective (rawSchurComplement_posDef T hT j hj).1.eigenvalues := by
  exact (full_atoms_coordinates _ (rawSchurComplement_posDef T hT j hj) _
    (raw_referenceAtomCount _ (rawSchurComplement_posDef T hT j hj)
      (rawSchur_tridiagonal T htri j hj) (rawSchur_adjacent_neg T htri hneg j hj))).1
end
end krylov.Envelope
