import krylov.Completion.StrictJacobiBand
import krylov.LinearAlgebra.LastSchurPivot
set_option autoImplicit false
/-!
Article: main_krylov, s5:fibre(b), genuine supplied-matrix last-diagonal band.
Use: compute original spectral completion endpoints directly in the supplied
physical coordinates, retaining singular whole endpoint matrices.
Source: reused closed scalar Schur band criterion on the true positive
leading shifts and exact finite last-site reindexing.
-/

namespace krylov.LinearAlgebra
noncomputable section
open Matrix krylov.Completion
variable {n : ℕ}

/-- Replace precisely the final diagonal entry of the supplied physical matrix.
Use: the literal supplied-Jacobi information family has no additional chosen frame.
Article: main_krylov, s5:fibre(b), physical last-diagonal completion. -/
def lastDiagonalUpdate (T : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (b : ℝ) :
    Matrix (Fin (n+1)) (Fin (n+1)) ℝ :=
  fun i j => if i=Fin.last n ∧ j=Fin.last n then b else T i j

/-- A literal final-diagonal update is exactly its physical last-site
rank-one update, with no orientation or normal-vector assumption.
Use: identify the actual original physical Lanczos completion on supplied matrices.
Article: main_krylov, s5:fibre(b), exact supplied last-diagonal update.
Proof: the two true coordinate deltas vanish except at the final diagonal;
there the added difference gives exactly the prescribed new value. -/
theorem last_diagonal_update_rankOne (T : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (b : ℝ) :
    lastDiagonalUpdate T b=T+(b-T (Fin.last n) (Fin.last n)) •
      vecMulVec (Pi.single (Fin.last n) 1) (Pi.single (Fin.last n) 1) := by
  ext i j
  by_cases hi : i=Fin.last n
  · subst i
    by_cases hj : j=Fin.last n
    · subst j
      simp only [lastDiagonalUpdate,and_self,ite_true,Matrix.add_apply,Matrix.smul_apply,vecMulVec_apply,
        Pi.single_eq_same,smul_eq_mul,mul_one]
      ring
    · simp [lastDiagonalUpdate,hj,vecMulVec_apply]
  · simp [lastDiagonalUpdate,hi,vecMulVec_apply]

/-- The actual last-site-first reindexing of a supplied symmetric matrix's
literal last-diagonal update has precisely its genuine scalar Schur blocks.
Use: all known leading and cross entries are actual supplied coordinates.
Article: main_krylov, s5:fibre(b), actual supplied scalar-corner decomposition.
Proof: evaluate the final coordinate and genuine leading coordinates in the
true finite equivalence; symmetry identifies the original cross row. -/
theorem last_diagonal_update_last_first (T : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hT : T.IsSymm) (b : ℝ) :
    let e : (Fin 1⊕Fin n) ≃ Fin (n+1) := (Equiv.sumComm (Fin 1) (Fin n)).trans finSumFinEquiv
    (lastDiagonalUpdate T b).submatrix e e=
      fromBlocks (scalarCorner b) (crossColumn (lastCross T))ᵀ (crossColumn (lastCross T)) (lastLeading T) := by
  dsimp only
  ext i j
  cases i with
  | inl i =>
    fin_cases i
    cases j with
    | inl j =>
      fin_cases j
      change lastDiagonalUpdate T b (Fin.last n) (Fin.last n)=b
      simp only [lastDiagonalUpdate,and_self,ite_true]
    | inr j =>
      change lastDiagonalUpdate T b (Fin.last n) (Fin.castSucc j)=T (Fin.castSucc j) (Fin.last n)
      simp only [lastDiagonalUpdate,Fin.castSucc_ne_last j,and_false,ite_false]
      exact congrFun (congrFun hT.eq (Fin.castSucc j)) (Fin.last n)
  | inr i =>
    cases j with
    | inl j =>
      fin_cases j
      change lastDiagonalUpdate T b (Fin.castSucc i) (Fin.last n)=T (Fin.castSucc i) (Fin.last n)
      simp only [lastDiagonalUpdate,Fin.castSucc_ne_last i,false_and,ite_false]
    | inr j =>
      change lastDiagonalUpdate T b (Fin.castSucc i) (Fin.castSucc j)=T (Fin.castSucc i) (Fin.castSucc j)
      simp only [lastDiagonalUpdate,Fin.castSucc_ne_last i,false_and,ite_false]

/-- Every literal supplied-matrix last-diagonal completion lies in the
original spectral band exactly between its true two inverse Schur endpoints.
Use: the actual matrices at both endpoints may have singular whole shifts;
only their genuinely positive known leading shifts are inverted.
Article: main_krylov, s5:fibre(b), supplied physical endpoint interval.
Proof: the exact real last-site-first decomposition preserves both shifted
positive forms. The proved closed scalar Schur band criterion gives the
literal two endpoint inequalities in the actual supplied coordinates. -/
theorem last_diagonal_update_band_iff (T : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hT : T.IsSymm)
    (mu upper b : ℝ) (hlo : (lastLeading T-mu • 1).PosDef) (hhi : (upper • 1-lastLeading T).PosDef) :
    (lastDiagonalUpdate T b-mu • 1).PosSemidef ∧ (upper • 1-lastDiagonalUpdate T b).PosSemidef ↔
      mu+lastCross T ⬝ᵥ ((lastLeading T-mu • 1)⁻¹*ᵥ lastCross T)≤b ∧
        b≤upper-lastCross T ⬝ᵥ ((upper • 1-lastLeading T)⁻¹*ᵥ lastCross T) := by
  let e : (Fin 1⊕Fin n) ≃ Fin (n+1) := (Equiv.sumComm (Fin 1) (Fin n)).trans finSumFinEquiv
  let C := lastDiagonalUpdate T b
  let J := fromBlocks (scalarCorner b) (crossColumn (lastCross T))ᵀ (crossColumn (lastCross T)) (lastLeading T)
  have hform : C.submatrix e e=J := last_diagonal_update_last_first T hT b
  have hl : (C-mu • 1).submatrix e e=J-mu • 1 := by
    simp only [Matrix.submatrix_sub,Matrix.submatrix_smul,Pi.sub_apply,Pi.smul_apply,Matrix.submatrix_one_equiv,hform]
  have hh : (upper • 1-C).submatrix e e=upper • 1-J := by
    simp only [Matrix.submatrix_sub,Matrix.submatrix_smul,Pi.sub_apply,Pi.smul_apply,Matrix.submatrix_one_equiv,hform]
  rw [← Matrix.posSemidef_submatrix_equiv e (M := C-mu • 1),hl,
    ← Matrix.posSemidef_submatrix_equiv e (M := upper • 1-C),hh]
  exact strict_scalar_band_iff (lastLeading T) (lastCross T) b mu upper hlo hhi

end
end krylov.LinearAlgebra
