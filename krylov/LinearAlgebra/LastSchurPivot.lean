import krylov.LinearAlgebra.SchurDeterminant
import krylov.LinearAlgebra.HiddenEntry
set_option autoImplicit false
/-!
Article: main_krylov, s5:fibre(a), literal last Schur pivot.
Use: identify the actual last inverse entry of a positive physical compression
with the reciprocal of its original leading-block Schur pivot.
Source: the proved genuine block Schur inverse, with all inverse domains derived
from positive definiteness, and mathlib's singleton inverse formula.
-/

namespace krylov.LinearAlgebra
noncomputable section
open Matrix
variable {n : ℕ}

/-- The true leading block of a square matrix with one remaining final site.
Use: the source's J0 is a principal part of the actual Jacobi compression.
Article: main_krylov, s5:fibre(a). -/
def lastLeading (J : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  J.submatrix Fin.castSucc Fin.castSucc

/-- The true last-column coupling to the original leading block.
Use: Jacobi tridiagonality later specializes this physical column to beta times
the last leading coordinate vector.
Article: main_krylov, s5:fibre(a). -/
def lastCross (J : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) : Fin n → ℝ :=
  fun i => J (Fin.castSucc i) (Fin.last n)

/-- The genuine scalar Schur correction determined by the whole leading data.
Use: identify the positivity threshold left invariant by a last-diagonal update.
Article: main_krylov, s5:fibre(a), sigma.
Proof: contract the actual inverse leading block with its real last coupling column. -/
def lastSchurCorrection (J : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) : ℝ :=
  lastCross J ⬝ᵥ ((lastLeading J)⁻¹*ᵥ lastCross J)

/-- The actual last inverse entry is the reciprocal of the true last Schur pivot.
Use: connect rank-one physical positivity and information radii to the article's
literal leading-block Schur coordinate.
Article: main_krylov, s5:fibre(a).
Proof: reindex the real positive matrix into its leading block and one-site
corner. Genuine block positivity supplies both inverse domains; the proved
block inverse and singleton inverse formula compute the actual final entry. -/
theorem last_schur_inverse (J : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hJ : J.PosDef) :
    J⁻¹ (Fin.last n) (Fin.last n)=(J (Fin.last n) (Fin.last n)-lastSchurCorrection J)⁻¹ := by
  let e : Fin n⊕Fin 1 ≃ Fin (n+1) := finSumFinEquiv
  let M := J.submatrix e e
  let L := lastLeading J
  let x := lastCross J
  let b := J (Fin.last n) (Fin.last n)
  have hform : M=fromBlocks L (crossColumn x) (crossColumn x)ᵀ (scalarCorner b) := by
    ext i j
    cases i with
    | inl i =>
      cases j with
      | inl j => rfl
      | inr j => fin_cases j;rfl
    | inr i =>
      fin_cases i
      cases j with
      | inl j =>
        change J (Fin.last n) (Fin.castSucc j)=J (Fin.castSucc j) (Fin.last n)
        exact congrFun (congrFun hJ.1.isSymm.eq (Fin.castSucc j)) (Fin.last n)
      | inr j => fin_cases j;rfl
  have hM : M.PosDef := hJ.submatrix e.injective
  have hblock : (fromBlocks L (crossColumn x) (crossColumn x)ᵀ (scalarCorner b)).PosDef := hform ▸ hM
  have hL : L.PosDef := hJ.submatrix (Fin.castSucc_injective n)
  have hS := block_schur_posDef L (crossColumn x) (crossColumn x)ᵀ (scalarCorner b) hblock
  have hinv := block_schur_inverse L (crossColumn x) (crossColumn x)ᵀ (scalarCorner b)
    (isUnit_iff_ne_zero.mpr hL.det_pos.ne') (isUnit_iff_ne_zero.mpr hS.det_pos.ne')
    (isUnit_iff_ne_zero.mpr hblock.det_pos.ne')
  rw [← hform] at hinv
  have hcorner := congrArg (fun T => T 0 0) hinv
  have hcross : (crossColumn x)ᵀ*L⁻¹*crossColumn x=scalarCorner (lastSchurCorrection J) :=
    crossColumn_quadratic x L⁻¹
  rw [hcross] at hcorner
  have hscalar := Matrix.inv_subsingleton (scalarCorner b-scalarCorner (lastSchurCorrection J))
  rw [hscalar] at hcorner
  simp only [Matrix.submatrix_apply,Matrix.diagonal_apply_eq,Matrix.sub_apply,scalarCorner,
    Ring.inverse_eq_inv] at hcorner
  dsimp only [M] at hcorner
  rw [Matrix.inv_submatrix_equiv] at hcorner
  exact hcorner

end
end krylov.LinearAlgebra
