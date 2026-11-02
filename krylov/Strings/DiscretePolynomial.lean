import krylov.Strings.DiscreteState
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
Article: `main_krylov`, `apC:eq:rec` and `apC:lem:stieltjes(a)`.
Construct the literal Stieltjes position and slope polynomials from the
actual masses and gaps. Their specialization at −1 is proved to be the
already constructed physical state; no polynomial recurrence is assumed.
-/

namespace krylov.Strings.DiscreteString
noncomputable section
open Polynomial
variable {N : ℕ} (S : DiscreteString N)

/-- The true finite string polynomial state, initialized after its unit atom. -/
def polynomialState : ℕ → ℝ[X] × ℝ[X]
  | 0 => (1, -X)
  | k + 1 =>
    let z := polynomialState k
    let q := z.1 + C (S.gap k) * z.2
    (q, z.2 - X * C (S.mass (k + 1)) * q)

/-- Position polynomial at the actual mass site. -/
def φPolynomial (k : ℕ) : ℝ[X] := (S.polynomialState k).1
/-- Slope polynomial immediately after the actual mass. -/
def pPolynomial (k : ℕ) : ℝ[X] := (S.polynomialState k).2

@[simp] theorem φPolynomial_zero : S.φPolynomial 0 = 1 := rfl
@[simp] theorem pPolynomial_zero : S.pPolynomial 0 = -X := rfl

/-- Exact source drift recurrence of the constructed position polynomials. -/
theorem φPolynomial_succ (k : ℕ) : S.φPolynomial (k + 1) =
    S.φPolynomial k + C (S.gap k) * S.pPolynomial k := rfl
/-- Exact source impulse recurrence of the constructed slope polynomials. -/
theorem pPolynomial_succ (k : ℕ) : S.pPolynomial (k + 1) =
    S.pPolynomial k - X * C (S.mass (k + 1)) * S.φPolynomial (k + 1) := rfl

/-- Position and slope at ζ=−1 agree with the same actual drift-impulse state. -/
theorem polynomialState_eval_neg_one (k : ℕ) :
    (S.φPolynomial k).eval (-1) = S.φ k ∧ (S.pPolynomial k).eval (-1) = S.p k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hφ : (S.φPolynomial (k + 1)).eval (-1) = S.φ (k + 1) := by
      rw [φPolynomial_succ, eval_add, eval_mul, eval_C, ih.1, ih.2, φ_succ]
    refine ⟨hφ, ?_⟩
    rw [pPolynomial_succ, eval_sub, eval_mul, eval_mul, eval_X, eval_C, ih.2, hφ, p_succ]
    ring

/-- At zero spectral energy the actual position is constant and the slope
vanishes, independently of the terminal Robin boundary condition. -/
theorem polynomialState_eval_zero (k : ℕ) :
    (S.φPolynomial k).eval 0 = 1 ∧ (S.pPolynomial k).eval 0 = 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hφ : (S.φPolynomial (k + 1)).eval 0 = 1 := by
      simp only [φPolynomial_succ, eval_add, eval_mul, eval_C, ih.1, ih.2, mul_zero, add_zero]
    exact ⟨hφ, by simp [pPolynomial_succ, ih.2]⟩

/-- The actual polynomial recurrences have their proper finite degree
bounds before spectral orthogonality is used to prove exact degree. -/
theorem polynomialState_degree_le (k : ℕ) :
    (S.φPolynomial k).natDegree ≤ k ∧ (S.pPolynomial k).natDegree ≤ k + 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hφ : (S.φPolynomial (k + 1)).natDegree ≤ k + 1 := by
      rw [φPolynomial_succ]
      apply (natDegree_add_le _ _).trans
      exact max_le (by omega) ((natDegree_C_mul_le _ _).trans ih.2)
    refine ⟨hφ, ?_⟩
    rw [pPolynomial_succ]
    apply (natDegree_sub_le _ _).trans
    apply max_le (by omega)
    calc
      _ ≤ (X * C (S.mass (k + 1))).natDegree + (S.φPolynomial (k + 1)).natDegree := natDegree_mul_le
      _ ≤ (X.natDegree + (C (S.mass (k + 1))).natDegree) + (k + 1) :=
        Nat.add_le_add (natDegree_mul_le) hφ
      _ = k + 1 + 1 := by simp; omega

end
end krylov.Strings.DiscreteString
