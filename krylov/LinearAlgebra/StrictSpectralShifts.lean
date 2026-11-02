import krylov.LinearAlgebra.NormOrder
import Mathlib.Algebra.Order.Star.Real
set_option autoImplicit false
/-!
Article: main_krylov, prop:phi(a), strict actual spectral endpoint tests.
Use: convert true positive shifted finite forms into genuine strict eigenvalue inequalities in the original matrix eigenbasis.
Source: actual orthogonal spectral coordinates, positive congruence and genuine diagonal positivity.
-/

namespace krylov.LinearAlgebra
noncomputable section
open Matrix chebyshev1
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Actual orthogonal spectral coordinates preserve genuine positive definiteness in both directions.
Use: Actual orthogonal spectral coordinates preserve genuine positive definiteness in both directions.
Article: main_krylov, prop:phi(a), strict actual spectral endpoint tests.
Proof: Use the true two-sided orthogonal inverses and positive congruences with their genuine injectivity domains. -/
theorem coordinates_posDef_iff {T : Matrix n n ℝ} (B : SpectralBasis T)
    (M : Matrix n n ℝ) : (B.coordinates M).PosDef ↔ M.PosDef := by
  -- The genuine orthogonal inverse supplies actual congruence injectivity in both directions.
  have hinj (Q : Matrix n n ℝ) (R : Matrix n n ℝ) (h : R*Q=1) : Function.Injective Q.mulVec := by
    intro x y he
    have hh := congrArg (fun v => R *ᵥ v) he
    simpa only [Matrix.mulVec_mulVec,h,Matrix.one_mulVec] using hh
  -- Undo the real coordinate congruence with the genuine complete orthogonal inverse.
  constructor
  · intro h
    have hp := h.mul_mul_conjTranspose_same (B := B.Q) (by
      rw [Matrix.vecMul_injective_iff_isUnit]
      exact (Matrix.isUnit_iff_isUnit_det _).mpr (by
        have hh := congrArg Matrix.det B.mul_transpose
        rw [Matrix.det_mul,Matrix.det_transpose,Matrix.det_one] at hh
        exact isUnit_iff_ne_zero.mpr (fun hz => by rw [hz,zero_mul] at hh;norm_num at hh)))
    have he : B.Q*B.coordinates M*B.Qᵀ=M := by
      unfold SpectralBasis.coordinates
      rw [← Matrix.mul_assoc,← Matrix.mul_assoc,B.mul_transpose,Matrix.one_mul,
        Matrix.mul_assoc,B.mul_transpose,Matrix.mul_one]
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial,he] using hp
  · intro h
    simpa only [SpectralBasis.coordinates,Matrix.conjTranspose_eq_transpose_of_trivial] using
      h.conjTranspose_mul_mul_same (B := B.Q) (hinj B.Q B.Qᵀ B.transpose_mul)

/-- A genuine positive lower shifted form is equivalent to true strict original eigenvalue lower bounds.
Use: A genuine positive lower shifted form is equivalent to true strict original eigenvalue lower bounds.
Article: main_krylov, prop:phi(a), strict actual spectral endpoint tests.
Proof: Diagonalize the actual original lower shift in its genuine spectral basis. -/
theorem positive_lower_shift_iff (T : Matrix n n ℝ) (hT : T.IsHermitian) (a : ℝ) :
    (T-a • 1).PosDef ↔ ∀ i,a<hT.eigenvalues i := by
  let B := SpectralBasis.ofHermitian T hT
  rw [← coordinates_posDef_iff B]
  have he : T-a • 1=(-a) • 1+T := by module
  rw [he,coordinates_lower_shift,Matrix.posDef_diagonal_iff]
  change (∀ i,0 < -a+hT.eigenvalues i) ↔ ∀ i,a<hT.eigenvalues i
  constructor <;> intro h i <;> linarith [h i]

/-- A genuine positive upper shifted form is equivalent to true strict original eigenvalue upper bounds.
Use: A genuine positive upper shifted form is equivalent to true strict original eigenvalue upper bounds.
Article: main_krylov, prop:phi(a), strict actual spectral endpoint tests.
Proof: Diagonalize the actual original upper shift in its genuine spectral basis. -/
theorem positive_upper_shift_iff (T : Matrix n n ℝ) (hT : T.IsHermitian) (b : ℝ) :
    (b • 1-T).PosDef ↔ ∀ i,hT.eigenvalues i<b := by
  let B := SpectralBasis.ofHermitian T hT
  rw [← coordinates_posDef_iff B,coordinates_upper_shift,Matrix.posDef_diagonal_iff]
  simp only [B,SpectralBasis.ofHermitian,sub_pos]
end
end krylov.LinearAlgebra
