import krylov.Tensor.FlatDyadicLog

/-!
Article: main_krylov, apG:flat, the operator-profile power lower bound.
Use: certify the printed 2/3 m^(3/2) bound for the actual finite sum of
square roots. A direct algebraic telescoping proof avoids improper endpoints.
Source: the usual monotone integral bound, here strengthened pointwise by
the exact nonnegative gap (sqrt(j+1)-sqrt j)²(sqrt(j+1)+2 sqrt j).
-/

namespace krylov.Tensor
noncomputable section
open Finset
open scoped BigOperators

/-- The exact discrete square-root power difference has the standard
three-halves upper bound. Article: main_krylov, apG:flat. -/
theorem flat_sqrt_power_step (j : ℕ) :
    2 * (((j+1 : ℕ) : ℝ) * Real.sqrt (j+1 : ℕ) - (j : ℝ) * Real.sqrt j) ≤
      3 * Real.sqrt (j+1 : ℕ) := by
  let a := Real.sqrt (j+1 : ℕ)
  let b := Real.sqrt (j : ℕ)
  have ha : a^2 = (j : ℝ)+1 := by
    dsimp only [a]
    simpa only [Nat.cast_add, Nat.cast_one] using Real.sq_sqrt (Nat.cast_nonneg (j+1))
  have hb : b^2 = (j : ℝ) := Real.sq_sqrt (Nat.cast_nonneg j)
  have ha3 : a^3 = ((j : ℝ)+1)*a := by rw [pow_succ, ha]
  have hb3 : b^3 = (j : ℝ)*b := by rw [pow_succ, hb]
  have hab : a*b^2 = a*(j : ℝ) := by rw [hb]
  have hgap : 0 ≤ (a-b)^2*(a+2*b) :=
    mul_nonneg (sq_nonneg _) (by dsimp only [a,b]; positivity)
  change 2 * (((j+1 : ℕ) : ℝ)*a - (j : ℝ)*b) ≤ 3*a
  push_cast
  nlinarith only [ha3, hb3, hab, hgap]

/-- The genuine finite square-root sum obeys the printed power lower bound.
Article: main_krylov, apG:flat. -/
theorem flat_sqrt_sum_lower (m : ℕ) :
    (2 / 3 : ℝ) * (m : ℝ)^((3 : ℝ)/2) ≤ ∑ j ∈ range m, Real.sqrt (j+1 : ℕ) := by
  have hs : 2 * (m : ℝ) * Real.sqrt m ≤ 3 * ∑ j ∈ range m, Real.sqrt (j+1 : ℕ) := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [sum_range_succ]
      have hb := flat_sqrt_power_step m
      push_cast at ih hb ⊢
      linarith
  have hp : (m : ℝ)^((3 : ℝ)/2) = (m : ℝ) * Real.sqrt m := by
    rw [show (3 : ℝ)/2 = 1 + 1/2 by norm_num,
      Real.rpow_add_of_nonneg (Nat.cast_nonneg _) (by norm_num) (by norm_num),
      Real.rpow_one, ← Real.sqrt_eq_rpow]
  rw [hp]
  linarith

end
end krylov.Tensor
