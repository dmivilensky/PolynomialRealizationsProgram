import bezout.Polynomial.Graded
import Mathlib.Algebra.Polynomial.Inductions

/-!
Article: bezout, Theorem 2.1 and its constructive converse in Appendix A.
Actual history coefficients synthesized from a normalized graded query family.
Use: the divided query `(1-q_s).divX` has degree strictly below `s`, hence
expands uniquely in the earlier queries; the terminal uses the entire family.
Proof: exact division by `X`, the degree drop of `divX`, and the graded
coordinate theorem. No invertibility or coefficient existence is assumed.
-/

namespace bezout
noncomputable section
open Polynomial
open scoped BigOperators

/-- A causal query family has constant value one at the zero Hessian.
Use: this normalization is precisely the affine-history condition of Theorem 2.1. -/
structure NormalizedFamily (N : ℕ) extends GradedFamily N where
  eval_zero : ∀ s, (poly s).eval 0 = 1

/-- The exact divided polynomial used for all rows and the final readout.
Use: turns affine-normalized queries into linear combinations of earlier queries. -/
def divided (p : ℝ[X]) : ℝ[X] := (1 - p).divX

/-- A normalized polynomial has no remainder in its divided-query identity.
Use: converts expansion coefficients back to the actual history recurrence. -/
theorem X_mul_divided (p : ℝ[X]) (hp : p.eval 0 = 1) : X * divided p = 1 - p := by
  have h := Polynomial.X_mul_divX_add (1 - p)
  have hzero : (1 - p).coeff 0 = 0 := by simp [coeff_zero_eq_eval_zero, hp]
  simpa only [divided, hzero, C_0, add_zero] using h

/-- Division by `X` lowers the degree below the original degree bound.
Use: makes the synthesized row depend only on the strictly earlier queries. -/
theorem degree_divided_lt (p : ℝ[X]) (n : ℕ)
    (hp : p.degree ≤ (n : WithBot ℕ)) : (divided p).degree < (n : WithBot ℕ) := by
  by_cases hz : 1 - p = 0
  · simp [divided, hz]
  · exact (Polynomial.degree_divX_lt hz).trans_le
      ((Polynomial.degree_sub_le _ _).trans (max_le (by simp) hp))

namespace NormalizedFamily
variable {N : ℕ} (Q : NormalizedFamily N)

/-- Coordinates of one causal history row, indexed by its earlier calls.
Use: the constructive converse supplies these exact real coefficients. -/
def row (s : Fin N) : Fin s.val → ℝ :=
  (Q.toGradedFamily.restrict s.val (Nat.le_of_lt s.isLt)).coordinates
    (divided (Q.poly s)) (degree_divided_lt _ _ (Q.degree_eq s).le)

/-- The synthesized row expands the divided query exactly.
Use: establishes the query recurrence of the reconstructed history. -/
theorem row_expansion (s : Fin N) :
    ∑ j : Fin s.val, Q.row s j • Q.poly (j.castLE (Nat.le_of_lt s.isLt)) =
      divided (Q.poly s) := by
  exact (Q.toGradedFamily.restrict s.val (Nat.le_of_lt s.isLt)).sum_coordinates _ _

/-- The actual affine recurrence encoded by each synthesized coefficient row.
Use: identifies the constructed history's nominal queries by causal induction. -/
theorem query_recurrence (s : Fin N) :
    Q.poly s = 1 - X *
      ∑ j : Fin s.val, C (Q.row s j) * Q.poly (j.castLE (Nat.le_of_lt s.isLt)) := by
  have h := X_mul_divided (Q.poly s) (Q.eval_zero s)
  rw [← Q.row_expansion s] at h
  simp only [smul_eq_C_mul] at h
  linear_combination h

/-- Coordinates of the terminal readout in the complete graded family.
Use: constructs output weights for any normalized terminal of degree at most `N`. -/
def weights (p : ℝ[X]) (hp : p.degree ≤ (N : WithBot ℕ)) : Fin N → ℝ :=
  Q.toGradedFamily.coordinates (divided p) (degree_divided_lt p N hp)

/-- The synthesized output weights implement exactly the prescribed terminal.
Use: establishes terminal exactness of the reconstructed causal history. -/
theorem terminal_recurrence (p : ℝ[X]) (hp : p.degree ≤ (N : WithBot ℕ))
    (hp0 : p.eval 0 = 1) :
    p = 1 - X * ∑ s, C (Q.weights p hp s) * Q.poly s := by
  have h := X_mul_divided p hp0
  rw [← Q.toGradedFamily.sum_coordinates (divided p) (degree_divided_lt p N hp)] at h
  simp only [smul_eq_C_mul] at h
  unfold weights
  linear_combination h

/-- Each row's coefficients are determined uniquely by its query recurrence.
Use: the uniqueness conclusion of Theorem 2.1 for all internal history rows. -/
theorem row_unique (s : Fin N) (c : Fin s.val → ℝ)
    (hc : Q.poly s = 1 - X *
      ∑ j : Fin s.val, C (c j) * Q.poly (j.castLE (Nat.le_of_lt s.isLt))) :
    c = Q.row s := by
  apply (Q.toGradedFamily.restrict s.val (Nat.le_of_lt s.isLt)).expansion_unique
  apply mul_left_cancel₀ (show (X : ℝ[X]) ≠ 0 by exact X_ne_zero)
  have heq := sub_right_inj.mp (hc.symm.trans (Q.query_recurrence s))
  simpa only [smul_eq_C_mul, GradedFamily.prefix_poly] using heq

/-- Terminal output coefficients are determined uniquely by the terminal recurrence.
Use: completes uniqueness of the reconstructed history's readout. -/
theorem weights_unique (p : ℝ[X]) (hp : p.degree ≤ (N : WithBot ℕ))
    (hp0 : p.eval 0 = 1) (c : Fin N → ℝ)
    (hc : p = 1 - X * ∑ s, C (c s) * Q.poly s) : c = Q.weights p hp := by
  apply Q.toGradedFamily.expansion_unique
  apply mul_left_cancel₀ (show (X : ℝ[X]) ≠ 0 by exact X_ne_zero)
  have := sub_right_inj.mp (hc.symm.trans (Q.terminal_recurrence p hp hp0))
  simpa only [smul_eq_C_mul] using this

end NormalizedFamily
end
end bezout
