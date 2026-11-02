import chebyshev1.Spectral.OperatorNorm
import Mathlib.Analysis.Matrix.Order
import Mathlib.Tactic.Linarith

/-!
Article: main_krylov, apA:galerkin(f) and canonical increment budgets.
Use: connect the actual Euclidean spectral norm with the two shifted positive
semidefinite forms, including equality and zero-dimensional boundary cases.
Source: the earlier article's proved spectral norm formula and mathlib's finite spectral theorem.
-/

namespace krylov.LinearAlgebra
noncomputable section
open Matrix chebyshev1 Polynomial
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Orthogonal spectral coordinates preserve positive semidefiniteness in both directions.
Use: shifted norm bounds reduce to genuine scalar eigenvalue inequalities.
Article: main_krylov, apA:galerkin(f), the two positive-semidefinite block tests.
Proof: compress by Q in one direction and by its actual inverse transpose in the other. -/
theorem coordinates_posSemidef_iff {A : Matrix ι ι ℝ} (B : SpectralBasis A)
    (X : Matrix ι ι ℝ) : (B.coordinates X).PosSemidef ↔ X.PosSemidef := by
  -- The reverse congruence uses the proved orthogonal inverse, with no spectral-gap premise.
  constructor
  · intro h
    have hp := h.mul_mul_conjTranspose_same B.Q
    have he : B.Q * B.coordinates X * B.Qᵀ = X := by
      unfold SpectralBasis.coordinates
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, B.mul_transpose, one_mul,
        Matrix.mul_assoc, B.mul_transpose, mul_one]
    simpa only [conjTranspose_eq_transpose_of_trivial, he] using hp
  · intro h
    simpa only [conjTranspose_eq_transpose_of_trivial, SpectralBasis.coordinates] using
      h.conjTranspose_mul_mul_same B.Q

/-- Spectral coordinates of a scalar shift of the identity minus the original matrix.
Use: both norm-ball boundaries are evaluated without assuming a strict spectral gap.
Article: main_krylov, apA:galerkin(f), ωI−K.
Proof: distribute the coordinate congruence and use the actual orthogonal diagonalization. -/
theorem coordinates_upper_shift {A : Matrix ι ι ℝ} (B : SpectralBasis A) (ω : ℝ) :
    B.coordinates (ω • (1 : Matrix ι ι ℝ) - A) = diagonal (fun i => ω - B.eigenvalues i) := by
  unfold SpectralBasis.coordinates
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_one, B.transpose_mul, B.diagonalize]
  ext i j
  by_cases hij : i = j <;> simp [hij]

/-- Spectral coordinates of the lower shifted positivity test.
Use: retain negative eigenvalues in the actual symmetric operator-norm ball.
Article: main_krylov, apA:galerkin(f), ωI+K.
Proof: the same coordinate calculation with addition instead of subtraction. -/
theorem coordinates_lower_shift {A : Matrix ι ι ℝ} (B : SpectralBasis A) (ω : ℝ) :
    B.coordinates (ω • (1 : Matrix ι ι ℝ) + A) = diagonal (fun i => ω + B.eigenvalues i) := by
  unfold SpectralBasis.coordinates
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_one, B.transpose_mul, B.diagonalize]
  ext i j
  by_cases hij : i = j <;> simp [hij]

/-- A symmetric spectral norm ball is exactly the pair of shifted positivity constraints.
Use: converts generalized Schur positivity into the article's exact uncertainty completion.
Article: main_krylov, apA:galerkin(f), ‖K‖≤ω iff ωI±K⪰0.
Proof: reuse the earlier spectral norm identity and compare each actual eigenvalue
with both endpoints of [−ω,ω]. -/
theorem spectral_norm_iff_shifted_posSemidef (A : Matrix ι ι ℝ) (hA : A.IsHermitian)
    {ω : ℝ} (hω : 0 ≤ ω) :
    opNorm A ≤ ω ↔ (ω • (1 : Matrix ι ι ℝ) - A).PosSemidef ∧
      (ω • (1 : Matrix ι ι ℝ) + A).PosSemidef := by
  -- The two endpoint tests are scalar inequalities on the same actual spectral basis.
  let B := SpectralBasis.ofHermitian A hA
  have hn : opNorm A = ‖B.eigenvalues‖ := by
    change opNorm A = ‖fun i => hA.eigenvalues i‖
    simpa only [Polynomial.aeval_X, Polynomial.eval_X] using opNorm_aeval_eq (X : ℝ[X]) A hA
  rw [hn, pi_norm_le_iff_of_nonneg hω,
    ← coordinates_posSemidef_iff B (ω • 1 - A),
    ← coordinates_posSemidef_iff B (ω • 1 + A),
    coordinates_upper_shift, coordinates_lower_shift,
    posSemidef_diagonal_iff, posSemidef_diagonal_iff]
  simp only [Real.norm_eq_abs, abs_le]
  constructor
  · intro h
    exact ⟨fun i => sub_nonneg.mpr (h i).2, fun i => by linarith [(h i).1]⟩
  · rintro ⟨hhi, hlo⟩ i
    exact ⟨by linarith [hlo i], by linarith [hhi i]⟩

end
end krylov.LinearAlgebra
