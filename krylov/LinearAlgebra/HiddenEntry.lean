import krylov.LinearAlgebra.BlockCompletion
import Mathlib.Tactic.FinCases

/-!
Article: Lemma A.1 [apA:galerkin] of krylov.tex.
Use: specialize the actual block completion fibre to its one-dimensional corner,
retaining the exact endpoint inverses instead of just a sufficient norm estimate.
Source: the proved generalized Schur completion, specialized to a scalar block.
-/

namespace krylov.LinearAlgebra
noncomputable section
open Matrix
open scoped Matrix MatrixOrder
variable {n : ℕ}

/-- A scalar as an actual one-dimensional symmetric matrix.
Use: its Loewner order is the ordinary order of the missing scalar entry.
Article: main_krylov, apA:galerkin(f), y. -/
def scalarCorner (y : ℝ) : Matrix (Fin 1) (Fin 1) ℝ := fun _ _ => y

/-- The actual rectangular cross column of a scalar-corner completion.
Use: its Schur quadratic form is xᵀA⁻¹x.
Article: main_krylov, apA:galerkin(f), cross block x. -/
def crossColumn (x : Fin n → ℝ) : Matrix (Fin n) (Fin 1) ℝ := fun i _ => x i

/-- Scalar-corner matrix order is exactly real order.
Use: convert the two matrix Schur bounds into the actual closed interval.
Article: main_krylov, apA:galerkin(f), scalar endpoint inequalities.
Proof: the sole eigenvalue of the difference is its scalar entry. -/
theorem scalarCorner_le_iff (a b : ℝ) : scalarCorner a ≤ scalarCorner b ↔ a ≤ b := by
  have he : scalarCorner b - scalarCorner a = diagonal (fun _ : Fin 1 => b - a) := by
    ext i j
    fin_cases i
    fin_cases j
    simp [scalarCorner]
  rw [Matrix.le_iff, he, posSemidef_diagonal_iff]
  simp only [sub_nonneg, forall_const]

/-- The compressed cross column has precisely the actual scalar quadratic form.
Use: identify both inverse endpoint corrections in the missing-entry interval.
Article: main_krylov, apA:galerkin(f), xᵀ(ωI±K)⁻¹x.
Proof: matrix multiplication is the transposed row pairing, associated across the operator. -/
theorem crossColumn_quadratic (x : Fin n → ℝ) (Z : Matrix (Fin n) (Fin n) ℝ) :
    (crossColumn x)ᵀ * Z * crossColumn x = scalarCorner (x ⬝ᵥ (Z *ᵥ x)) := by
  ext i j
  change (x ᵥ* Z) ⬝ᵥ x = x ⬝ᵥ (Z *ᵥ x)
  exact (dotProduct_mulVec x Z x).symm

/-- The missing scalar entries form exactly the printed closed interval, possibly empty.
Use: the admissible interval is derived from the full actual spectral-norm constraint.
Article: main_krylov, apA:galerkin(f), the two inverse endpoint formulas.
Proof: specialize the strict block completion to one corner and identify its two
Schur quadratic forms and its real order. -/
theorem hidden_entry_interval (K : Matrix (Fin n) (Fin n) ℝ) (hK : K.IsSymm)
    (x : Fin n → ℝ) {ω : ℝ} (hn : chebyshev1.opNorm K < ω) (y : ℝ) :
    chebyshev1.opNorm (fromBlocks (scalarCorner y) (crossColumn x)ᵀ (crossColumn x) K) ≤ ω ↔
      -ω + x ⬝ᵥ ((ω • 1 + K)⁻¹ *ᵥ x) ≤ y ∧
      y ≤ ω - x ⬝ᵥ ((ω • 1 - K)⁻¹ *ᵥ x) := by
  rw [strict_block_completion_iff _ (by rfl) K hK _ hn,
    crossColumn_quadratic, crossColumn_quadratic]
  have hlo : -ω • (1 : Matrix (Fin 1) (Fin 1) ℝ) +
      scalarCorner (x ⬝ᵥ ((ω • 1 + K)⁻¹ *ᵥ x)) =
      scalarCorner (-ω + x ⬝ᵥ ((ω • 1 + K)⁻¹ *ᵥ x)) := by
    ext i j
    fin_cases i
    fin_cases j
    simp [scalarCorner]
  have hhi : ω • (1 : Matrix (Fin 1) (Fin 1) ℝ) -
      scalarCorner (x ⬝ᵥ ((ω • 1 - K)⁻¹ *ᵥ x)) =
      scalarCorner (ω - x ⬝ᵥ ((ω • 1 - K)⁻¹ *ᵥ x)) := by
    ext i j
    fin_cases i
    fin_cases j
    simp [scalarCorner]
  -- The one-dimensional Loewner bounds are exactly the two scalar endpoint inequalities.
  rw [hlo, hhi, scalarCorner_le_iff, scalarCorner_le_iff]

/-- The two endpoint resolvents have the exact sum and difference used by the hidden-entry centre.
Use: compute the interval centre, half-width and nonemptiness in the printed closed form.
Article: main_krylov, apA:galerkin(f), (ω²I−K²)⁻¹.
Proof: factor the actual quadratic gap as the product of the two invertible shifts;
the standard inverse sum/difference identities and a proved commutation give the formulas. -/
theorem shifted_inverse_sum_sub (K : Matrix (Fin n) (Fin n) ℝ) (hK : K.IsSymm)
    {ω : ℝ} (hn : chebyshev1.opNorm K < ω) :
    ((ω • 1 + K)⁻¹ + (ω • 1 - K)⁻¹ = (2 * ω) • (ω^2 • 1 - K^2)⁻¹) ∧
      ((ω • 1 + K)⁻¹ - (ω • 1 - K)⁻¹ = (-2 : ℝ) • (K * (ω^2 • 1 - K^2)⁻¹)) := by
  let P := ω • (1 : Matrix (Fin n) (Fin n) ℝ) + K
  let M := ω • (1 : Matrix (Fin n) (Fin n) ℝ) - K
  have hs := strict_shifted_posDef K hK hn
  have hP : IsUnit P.det := isUnit_iff_ne_zero.mpr hs.2.det_pos.ne'
  have hM : IsUnit M.det := isUnit_iff_ne_zero.mpr hs.1.det_pos.ne'
  have hu : IsUnit P ↔ IsUnit M := iff_of_true
    ((Matrix.isUnit_iff_isUnit_det _).mpr hP) ((Matrix.isUnit_iff_isUnit_det _).mpr hM)
  have hD : M * P = ω^2 • 1 - K^2 := by
    simp only [P, M, Matrix.sub_mul, Matrix.mul_add, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_one, Matrix.one_mul, pow_two]
    module
  have hsum : P + M = (2 * ω) • (1 : Matrix (Fin n) (Fin n) ℝ) := by dsimp [P, M]; module
  have hsub : M - P = (-2 : ℝ) • K := by dsimp [P, M]; module
  -- The inverse shift commutes with K because both its left and right inverse equations hold.
  have hc : P⁻¹ * K = K * P⁻¹ := by
    have hl := nonsing_inv_mul P hP
    have hr := mul_nonsing_inv P hP
    simp only [P, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_one, Matrix.one_mul] at hl hr
    exact add_left_cancel (hl.trans hr.symm)
  have hi : (ω^2 • (1 : Matrix (Fin n) (Fin n) ℝ) - K^2)⁻¹ = P⁻¹ * M⁻¹ := by
    rw [← hD, Matrix.mul_inv_rev]
  constructor
  · change P⁻¹ + M⁻¹ = _
    rw [Matrix.inv_add_inv hu, hsum, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hi]
  · change P⁻¹ - M⁻¹ = _
    rw [Matrix.inv_sub_inv hu, hsub, Matrix.mul_smul, Matrix.smul_mul, hc, hi, Matrix.mul_assoc]

/-- The actual inverse-gap quadratic form gives both the interval centre and half-width.
Use: all scalar completion formulas refer to the genuine endpoint and quadratic inverses.
Article: main_krylov, apA:galerkin(f), centre and half-length.
Proof: evaluate the proved resolvent sum and difference on x and simplify the scalar halves. -/
theorem hidden_entry_centre_width (K : Matrix (Fin n) (Fin n) ℝ) (hK : K.IsSymm)
    (x : Fin n → ℝ) {ω : ℝ} (hn : chebyshev1.opNorm K < ω) :
    let lower := -ω + x ⬝ᵥ ((ω • 1 + K)⁻¹ *ᵥ x)
    let upper := ω - x ⬝ᵥ ((ω • 1 - K)⁻¹ *ᵥ x)
    (lower + upper) / 2 = -(x ⬝ᵥ ((K * (ω^2 • 1 - K^2)⁻¹) *ᵥ x)) ∧
      (upper - lower) / 2 = ω - ω * (x ⬝ᵥ ((ω^2 • 1 - K^2)⁻¹ *ᵥ x)) := by
  -- Evaluate the actual matrix resolvents on the same cross vector before scalar simplification.
  obtain ⟨hs, hd⟩ := shifted_inverse_sum_sub K hK hn
  have hsum := congrArg (fun Z : Matrix (Fin n) (Fin n) ℝ => x ⬝ᵥ (Z *ᵥ x)) hs
  have hsub := congrArg (fun Z : Matrix (Fin n) (Fin n) ℝ => x ⬝ᵥ (Z *ᵥ x)) hd
  simp only [add_mulVec, sub_mulVec, Matrix.smul_mulVec, dotProduct_add, dotProduct_sub,
    dotProduct_smul, smul_eq_mul] at hsum hsub
  dsimp only
  constructor <;> linarith

/-- A bounded hidden entry exists exactly under the printed inverse-gap feasibility condition.
Use: the interval is nonempty precisely when its proved half-width is nonnegative.
Article: main_krylov, apA:galerkin(f), xᵀ(ω²I−K²)⁻¹x≤1.
Proof: an actual scalar lies in both endpoint bounds iff the lower endpoint
does not exceed the upper; the proved width identity and ω>0 give the condition. -/
theorem hidden_entry_feasible (K : Matrix (Fin n) (Fin n) ℝ) (hK : K.IsSymm)
    (x : Fin n → ℝ) {ω : ℝ} (hn : chebyshev1.opNorm K < ω) :
    (∃ y : ℝ, chebyshev1.opNorm
      (fromBlocks (scalarCorner y) (crossColumn x)ᵀ (crossColumn x) K) ≤ ω) ↔
      x ⬝ᵥ ((ω^2 • 1 - K^2)⁻¹ *ᵥ x) ≤ 1 := by
  -- The positive gap radius turns nonnegativity of the actual interval width into feasibility.
  have hω : 0 < ω := (chebyshev1.opNorm_nonneg K).trans_lt hn
  have hw := (hidden_entry_centre_width K hK x hn).2
  simp only [hidden_entry_interval K hK x hn]
  constructor
  · rintro ⟨y, hlo, hhi⟩
    nlinarith
  · intro hq
    refine ⟨-ω + x ⬝ᵥ ((ω • 1 + K)⁻¹ *ᵥ x), le_rfl, ?_⟩
    nlinarith

end
end krylov.LinearAlgebra
