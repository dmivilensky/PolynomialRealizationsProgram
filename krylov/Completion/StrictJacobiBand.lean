import krylov.Completion.ScalarSchur
import krylov.LinearAlgebra.HiddenEntry
set_option autoImplicit false
/-!
Article: main_krylov, s5:fibre(b), closed spectral Schur interval.
Use: derive the exact two ordinary-inverse endpoint tests after genuine
irreducibility has supplied the strict leading spectral shifts.
Source: the already proved generalized Schur criterion (Albert69); positivity
of the real leading blocks discharges all singular range conditions.
-/

namespace krylov.Completion
noncomputable section
open Matrix krylov.LinearAlgebra
variable {p : ℕ}

/-- A strictly positive actual leading block reduces the scalar Schur test
to its ordinary-inverse quadratic endpoint, including a singular whole endpoint.
Use: no nonsingular whole-matrix assumption excludes Gauss--Radau endpoint completions.
Article: main_krylov, s5:fibre(b).
Proof: genuine leading positivity gives an actual inverse and surjectivity;
the proved generalized Schur test retains the closed scalar inequality. -/
theorem strict_scalar_schur_iff (H : Matrix (Fin p) (Fin p) ℝ) (hH : H.PosDef)
    (x : Fin p → ℝ) (c : ℝ) :
    (fromBlocks (scalarCorner c) (crossColumn x)ᵀ (crossColumn x) H).PosSemidef ↔
      x ⬝ᵥ (H⁻¹*ᵥ x)≤c := by
  have hr : LinearMap.range (crossColumn x).mulVecLin≤LinearMap.range H.mulVecLin := by
    intro v _
    refine ⟨H⁻¹*ᵥ v,?_⟩
    change H*ᵥ (H⁻¹*ᵥ v)=v
    rw [mulVec_mulVec,mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hH.det_pos.ne'),one_mulVec]
  have he := scalar_schur_iff H hH.posSemidef (crossColumn x) c
  rw [pseudoinverse_eq_inv _ _ (isUnit_iff_ne_zero.mpr hH.det_pos.ne'),crossColumn_quadratic] at he
  have hcorner : (Matrix.of (fun _ _ : Fin 1 => c))=scalarCorner c := by ext i j;rfl
  rw [hcorner] at he
  simpa only [hr,true_and,scalarCorner] using he

/-- The actual scalar-corner lower spectral shift preserves the true cross
column and shifts only its real corner and leading block.
Use: share the same physical spectral pencil in interval and endpoint proofs.
Article: main_krylov, s5:fibre(b).
Proof: inspect its four genuine finite blocks; the singleton identity is scalar. -/
theorem scalar_corner_lower_shift (H : Matrix (Fin p) (Fin p) ℝ) (x : Fin p → ℝ)
    (b mu : ℝ) :
    fromBlocks (scalarCorner b) (crossColumn x)ᵀ (crossColumn x) H-mu • 1=
      fromBlocks (scalarCorner (b-mu)) (crossColumn x)ᵀ (crossColumn x) (H-mu • 1) := by
  ext i j
  cases i <;> cases j <;> simp [scalarCorner,Matrix.fromBlocks,Matrix.one_apply]
  exact fun h => (h (Subsingleton.elim _ _)).elim

/-- The actual upper spectral shift negates the true cross column and shifts
its real scalar corner and leading block.
Use: retain the exact same upper endpoint pencil for feasibility and node proofs.
Article: main_krylov, s5:fibre(b).
Proof: inspect its four actual blocks, including the singleton identity. -/
theorem scalar_corner_upper_shift (H : Matrix (Fin p) (Fin p) ℝ) (x : Fin p → ℝ)
    (b upper : ℝ) :
    upper • 1-fromBlocks (scalarCorner b) (crossColumn x)ᵀ (crossColumn x) H=
      fromBlocks (scalarCorner (upper-b)) (crossColumn (-x))ᵀ (crossColumn (-x)) (upper • 1-H) := by
  ext i j
  cases i <;> cases j <;> simp [scalarCorner,crossColumn,Matrix.fromBlocks,Matrix.one_apply]
  exact fun h => (h (Subsingleton.elim _ _)).elim

/-- The actual scalar-corner spectral-band test is precisely the two closed
ordinary-inverse Schur endpoint inequalities.
Use: construct the true Gauss--Radau segment from strict original leading
shifts, keeping both whole-matrix spectral endpoints admissible.
Article: main_krylov, s5:fibre(b).
Proof: subtract the real lower spectral form and upper spectral form from the
actual block matrix, then apply both true positive-leading scalar Schur tests.
The upper cross column changes sign and its real inverse quadratic form does not. -/
theorem strict_scalar_band_iff (H : Matrix (Fin p) (Fin p) ℝ) (x : Fin p → ℝ)
    (b mu upper : ℝ) (hlo : (H-mu • 1).PosDef) (hhi : (upper • 1-H).PosDef) :
    let J := fromBlocks (scalarCorner b) (crossColumn x)ᵀ (crossColumn x) H
    (J-mu • 1).PosSemidef ∧ (upper • 1-J).PosSemidef ↔
      mu+x ⬝ᵥ ((H-mu • 1)⁻¹*ᵥ x)≤b ∧ b≤upper-x ⬝ᵥ ((upper • 1-H)⁻¹*ᵥ x) := by
  dsimp only
  rw [scalar_corner_lower_shift,scalar_corner_upper_shift,
    strict_scalar_schur_iff _ hlo,strict_scalar_schur_iff _ hhi]
  simp only [mulVec_neg,dotProduct_neg,neg_dotProduct,neg_neg]
  constructor <;> rintro ⟨h1,h2⟩ <;> constructor <;> linarith

end
end krylov.Completion
