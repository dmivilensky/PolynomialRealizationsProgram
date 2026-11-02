import krylov.Tensor.FlatDyadicLog

/-!
Article: main_krylov, apG:flat, the genuine squared-prefix contraction bound.
Use: apply Banach's proved cubic identity to the actual finite dyadic
expansion and its actual rank-one cost. No tensor estimate is an assumption.
Source: the actual binary decomposition, finite Cauchy--Schwarz and Banach.
-/

namespace krylov.Tensor
noncomputable section
open Finset krylov.Functions
open scoped BigOperators InnerProductSpace
variable {N L : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The cost of the real dyadic block decomposition is exactly the iterated
sum of its actual level-pair costs. Article: main_krylov, apG:flat. -/
theorem flatDyadic_cost_levels (e : Fin N → E) (u : E) :
    (∑ p : DyadicPrefixIndex L, ∑ q : DyadicPrefixIndex L,
      ‖flagComponent e (dyadicHalf N p.1.val p.2.val true ∩
        dyadicHalf N q.1.val q.2.val true) u‖ *
        ‖dyadicLeftVector e p‖ * ‖dyadicLeftVector e q‖) =
      ∑ k : Fin L, ∑ l : Fin L, flatDyadicLayerCost e k l u := by
  simp only [DyadicPrefixIndex, Fintype.sum_sigma]
  apply sum_congr rfl
  intro k _
  rw [Finset.sum_comm]
  rfl

variable [FiniteDimensional ℝ E]

/-- The real squared-prefix contraction obeys the genuine dyadic bound.
Article: main_krylov, apG:flat, the X₁ estimate. -/
theorem abs_flatPrefixContraction_le (e : Fin N → E) (he : Orthonormal ℝ e)
    (T : SymmetricCubic E) {C : ℝ} (hC : 0 ≤ C)
    (hd : ∀ x : E, ‖x‖ = 1 → |T.form x x x| ≤ C)
    (hN : N ≤ 2 ^ L) (u : E) :
    |flatPrefixContraction e T u| ≤
      C * (2 * (L : ℝ) * (2 : ℝ) ^ L / (Real.sqrt 2 - 1)) * ‖u‖ := by
  rw [flatPrefixContraction_dyadic e T hN]
  calc
    _ ≤ ∑ p : DyadicPrefixIndex L, ∑ q : DyadicPrefixIndex L,
        |T.form (flagComponent e (dyadicHalf N p.1.val p.2.val true ∩
          dyadicHalf N q.1.val q.2.val true) u) (dyadicLeftVector e p) (dyadicLeftVector e q)| :=
      (abs_sum_le_sum_abs _ _).trans (sum_le_sum (fun p _ => abs_sum_le_sum_abs _ _))
    _ ≤ C * (∑ p : DyadicPrefixIndex L, ∑ q : DyadicPrefixIndex L,
        ‖flagComponent e (dyadicHalf N p.1.val p.2.val true ∩
          dyadicHalf N q.1.val q.2.val true) u‖ *
          ‖dyadicLeftVector e p‖ * ‖dyadicLeftVector e q‖) := by
      simp only [mul_sum]
      apply sum_le_sum
      intro p _
      apply sum_le_sum
      intro q _
      simpa only [mul_assoc] using cubic_diagonal_bound T C hd
        (flagComponent e (dyadicHalf N p.1.val p.2.val true ∩
          dyadicHalf N q.1.val q.2.val true) u) (dyadicLeftVector e p) (dyadicLeftVector e q)
    _ ≤ _ := by
      rw [flatDyadic_cost_levels]
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (flatDyadic_total_cost_le e he u) hC

end
end krylov.Tensor
