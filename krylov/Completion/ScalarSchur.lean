import krylov.LinearAlgebra.Schur
import Mathlib.Analysis.Matrix.Order
set_option autoImplicit false
/-!
Article: main_krylov, thm:radau, singular compressed curvature interval.
Use: compute the exact closed interval before reconstructing physical endpoint
completions; shifted blocks may be singular and retain their range conditions.
Source: Albert69, generalized Schur criterion, already proved in this project.
-/

namespace krylov.Completion
noncomputable section
open Matrix krylov.LinearAlgebra
variable {p : ℕ}

/-- A scalar block is positive semidefinite exactly when its actual entry is nonnegative.
Use: read the scalar Schur remainder without excluding zero or singular endpoints.
Article: main_krylov, thm:radau.
Proof: a one-dimensional matrix is its diagonal, and diagonal positivity is
the entrywise scalar condition. -/
theorem scalar_block_positive (M : Matrix (Fin 1) (Fin 1) ℝ) :
    M.PosSemidef ↔ 0≤M 0 0 := by
  have he : M=diagonal (fun _ : Fin 1 => M 0 0) := by
    ext i j
    fin_cases i
    fin_cases j
    simp
  rw [he,posSemidef_diagonal_iff]
  simp

/-- The scalar Schur test with an arbitrary singular positive old block.
Use: the cross-block range condition is a necessary part of completion feasibility.
Article: main_krylov, thm:radau.
Proof: apply the proved full generalized Schur equivalence, then evaluate its
one-dimensional positive remainder. -/
theorem scalar_schur_iff (H : Matrix (Fin p) (Fin p) ℝ) (hH : H.PosSemidef)
    (b : Matrix (Fin p) (Fin 1) ℝ) (c : ℝ) :
    (fromBlocks (Matrix.of (fun _ _ : Fin 1 => c)) bᵀ b H).PosSemidef ↔
      (LinearMap.range b.mulVecLin≤LinearMap.range H.mulVecLin) ∧
        (bᵀ*pseudoinverse H hH.1*b) 0 0≤c := by
  rw [generalized_schur_iff _ H hH b,scalar_block_positive]
  simp only [Matrix.sub_apply]
  exact and_congr_right (fun _ => sub_nonneg)

/-- The actual compressed metric of a new direction followed by the old window.
Use: retain the nonzero Euclidean cross block even when the operator cross
block is constrained to vanish by conjugacy.
Article: main_krylov, thm:radau.
Proof: assemble its physical squared length, actual cross coordinates and old Gram. -/
def windowAugmentedGram (G : Matrix (Fin p) (Fin p) ℝ)
    (b : Matrix (Fin p) (Fin 1) ℝ) (D : ℝ) :
    Matrix (Fin 1 ⊕ Fin p) (Fin 1 ⊕ Fin p) ℝ :=
  fromBlocks (fun _ _ => D) bᵀ b G

/-- The prescribed compressed operator has a free scalar curvature and zero
cross block with the already conjugate old window.
Use: this is the actual pair of Gram and conjugacy constraints.
Article: main_krylov, thm:radau.
Proof: put the unknown curvature and known old model on their diagonal blocks. -/
def windowCurvatureForm (T : Matrix (Fin p) (Fin p) ℝ) (c : ℝ) :
    Matrix (Fin 1 ⊕ Fin p) (Fin 1 ⊕ Fin p) ℝ :=
  fromBlocks (fun _ _ => c) 0 0 T

/-- The full closed lower spectral test is a singular Schur lower-curvature bound.
Use: derive the exact lower endpoint while preserving the necessary range condition.
Article: main_krylov, thm:radau.
Proof: the shifted metric has cross block −μb; its squared Schur correction is
μ² times the genuine Moore--Penrose quadratic form. -/
theorem lower_curvature_test (G T : Matrix (Fin p) (Fin p) ℝ)
    (b : Matrix (Fin p) (Fin 1) ℝ) (D c mu : ℝ)
    (h : (T-mu • G).PosSemidef) :
    (windowCurvatureForm T c-mu • windowAugmentedGram G b D).PosSemidef ↔
      (LinearMap.range ((-mu) • b).mulVecLin≤LinearMap.range (T-mu • G).mulVecLin) ∧
        mu*D+mu^2*(bᵀ*pseudoinverse (T-mu • G) h.1*b) 0 0≤c := by
  have he : windowCurvatureForm T c-mu • windowAugmentedGram G b D=
      fromBlocks (Matrix.of (fun _ _ : Fin 1 => c-mu*D)) (((-mu) • b)ᵀ) ((-mu) • b) (T-mu • G) := by
    ext i j
    cases i <;> cases j <;> simp [windowCurvatureForm,windowAugmentedGram,Matrix.fromBlocks]
  rw [he,scalar_schur_iff _ h]
  simp only [transpose_smul,Matrix.smul_mul,Matrix.mul_smul,
    Matrix.smul_apply,smul_eq_mul]
  exact and_congr_right (fun _ => by constructor <;> intro hbound <;> nlinarith)

/-- The full closed upper spectral test is a singular Schur upper-curvature bound.
Use: derive the exact upper endpoint, including singular endpoint blocks.
Article: main_krylov, thm:radau.
Proof: shift the other endpoint and apply the same genuine scalar Schur test. -/
theorem upper_curvature_test (G T : Matrix (Fin p) (Fin p) ℝ)
    (b : Matrix (Fin p) (Fin 1) ℝ) (D c L : ℝ)
    (h : (L • G-T).PosSemidef) :
    (L • windowAugmentedGram G b D-windowCurvatureForm T c).PosSemidef ↔
      (LinearMap.range (L • b).mulVecLin≤LinearMap.range (L • G-T).mulVecLin) ∧
        c≤L*D-L^2*(bᵀ*pseudoinverse (L • G-T) h.1*b) 0 0 := by
  have he : L • windowAugmentedGram G b D-windowCurvatureForm T c=
      fromBlocks (Matrix.of (fun _ _ : Fin 1 => L*D-c)) ((L • b)ᵀ) (L • b) (L • G-T) := by
    ext i j
    cases i <;> cases j <;> simp [windowCurvatureForm,windowAugmentedGram,Matrix.fromBlocks]
  rw [he,scalar_schur_iff _ h]
  simp only [transpose_smul,Matrix.smul_mul,Matrix.mul_smul,
    Matrix.smul_apply,smul_eq_mul]
  exact and_congr_right (fun _ => by constructor <;> intro hbound <;> nlinarith)

end
end krylov.Completion
