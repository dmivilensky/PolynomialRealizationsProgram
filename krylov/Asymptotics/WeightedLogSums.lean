import krylov.Asymptotics.StepCoordinates

/-!
Article: main_krylov, upper bound in thm:limit after apC:lem:step.
Use: actual post-mass energy weights decrease, and Abel summation controls
actual position increments by the bounded ratio plus energy/slope increments.
Source: the exact ratio identity and the proved elementary Abel inequality.
-/
namespace krylov.Asymptotics
noncomputable section
open Real Finset
open krylov.Strings
open scoped BigOperators

namespace DiscreteString
variable {N : ℕ} (S : krylov.Strings.DiscreteString N)

/-- Actual source weight of the next post-mass energy. -/
def energyWeight (γ : ℝ) (j : ℕ) : ℝ := S.K (j + 1) ^ (-γ)
/-- A weighted sum over the actual `N` edges. -/
def weightedSum (γ : ℝ) (f : ℕ → ℝ) : ℝ := ∑ j ∈ range N, energyWeight S γ j * f j

/-- Each actual energy weight is positive and at most one. -/
theorem energyWeight_bounds {γ : ℝ} (hγ : 0 ≤ γ) {j : ℕ} (hj : j < N) :
    0 < energyWeight S γ j ∧ energyWeight S γ j ≤ 1 := by
  have hK := (S.state_bounds (j + 1) (by omega)).2.2.1
  refine ⟨Real.rpow_pos_of_pos (by linarith) _, ?_⟩
  simpa only [energyWeight, Real.one_rpow] using Real.rpow_le_rpow_of_nonpos zero_lt_one hK (neg_nonpos.mpr hγ)

/-- Energy monotonicity gives decreasing actual weights. -/
theorem energyWeight_succ_le {γ : ℝ} (hγ : 0 ≤ γ) {j : ℕ} (hj : j + 1 < N) :
    energyWeight S γ (j + 1) ≤ energyWeight S γ j := by
  have hK := (S.state_bounds (j + 1) hj.le).2.2.1
  have hinc := (coordinates_strict S hj).2.2.le
  exact Real.rpow_le_rpow_of_nonpos (by linarith) hinc (neg_nonpos.mpr hγ)

/-- The actual weighted energy-log sum obeys the sharp uniform bound. -/
theorem weighted_energyLog_le {γ : ℝ} (hγ : 0 < γ) :
    weightedSum S γ (energyLog S) ≤ 1 / γ := weighted_energy_log_sum_le S hγ

/-- Actual nonnegative slope increments have a nonnegative weighted sum. -/
theorem weighted_slopeLog_nonneg {γ : ℝ} (hγ : 0 ≤ γ) :
    0 ≤ weightedSum S γ (slopeLog S) := by
  apply sum_nonneg
  intro j hj
  exact mul_nonneg (energyWeight_bounds S hγ (mem_range.mp hj)).1.le
    (log_bounds S (mem_range.mp hj)).2.1.le

/-- Actual Abel summation under the spectral ratio bound. -/
theorem weighted_ratio_increment_le {γ Λ : ℝ} (hγ : 0 ≤ γ) (hΛ : 0 < Λ)
    (hprod : ∀ j < N, 1 ≤ Λ * S.mass (j + 1) * S.gap j) :
    weightedSum S γ (fun j ↦ log (S.ratio (j + 1)) - log (S.ratio j)) ≤ log (1 + Λ) := by
  by_cases hN : N = 0
  · subst N
    simp [weightedSum]
    exact log_nonneg (by linarith)
  have hNpos : 0 < N := Nat.pos_of_ne_zero hN
  let f : ℕ → ℝ := fun j ↦ log (S.ratio j)
  let g : ℕ → ℝ := fun j ↦ S.K (min (j + 1) N) ^ (-γ)
  have hf₀ : f 0 = 0 := by simp [f, krylov.Strings.DiscreteString.ratio]
  have hf : ∀ j ≤ N, f j ≤ log (1 + Λ) := by
    intro j hj
    exact log_le_log (by linarith [(S.ratio_ge_one j hj)]) (ratio_bounds S hΛ hprod hj).2
  have hg : ∀ j ≤ N, 0 ≤ g j := by
    intro j _
    have hK := (S.state_bounds (min (j + 1) N) (min_le_right _ _)).2.2.1
    exact Real.rpow_nonneg (by linarith) _
  have hdec : ∀ j, j + 1 < N → g (j + 1) ≤ g j := by
    intro j hj
    dsimp [g]
    rw [min_eq_left (show j + 1 + 1 ≤ N by omega), min_eq_left hj.le]
    exact energyWeight_succ_le S hγ hj
  have hAbel := weighted_increment_sum_le N hf₀ hf hg hdec
  have heq : weightedSum S γ (fun j ↦ log (S.ratio (j + 1)) - log (S.ratio j)) =
      ∑ j ∈ range N, g j * (f (j + 1) - f j) := by
    apply sum_congr rfl
    intro j hj
    simp only [energyWeight, g, f, min_eq_left (Nat.succ_le_of_lt (mem_range.mp hj))]
  rw [heq]
  apply hAbel.trans
  have hg₀ : g 0 ≤ 1 := by
    dsimp [g]
    rw [min_eq_left hNpos]
    exact (energyWeight_bounds S hγ hNpos).2
  exact mul_le_of_le_one_left (log_nonneg (by linarith)) hg₀

/-- The printed Abel estimate for the actual drift-log sum. -/
theorem weighted_driftLog_le {γ Λ : ℝ} (hγ : 0 ≤ γ) (hΛ : 0 < Λ)
    (hprod : ∀ j < N, 1 ≤ Λ * S.mass (j + 1) * S.gap j) :
    weightedSum S γ (driftLog S) ≤ log (1 + Λ) +
      weightedSum S γ (energyLog S) - weightedSum S γ (slopeLog S) := by
  have heq : weightedSum S γ (driftLog S) =
      weightedSum S γ (fun j ↦ log (S.ratio (j + 1)) - log (S.ratio j)) +
        weightedSum S γ (energyLog S) - weightedSum S γ (slopeLog S) := by
    unfold weightedSum
    rw [← sum_add_distrib, ← sum_sub_distrib]
    apply sum_congr rfl
    intro j hj
    have hh := ratio_log_increment S (mem_range.mp hj)
    linear_combination -(energyWeight S γ j) * hh
  rw [heq]
  linarith only [weighted_ratio_increment_le S hγ hΛ hprod]

end DiscreteString
end
end krylov.Asymptotics
