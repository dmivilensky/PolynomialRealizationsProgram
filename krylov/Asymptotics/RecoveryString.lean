import krylov.Strings.DiscreteState

/-!
Article: main_krylov, lower bound in thm:limit.
Use: construct the genuine finite recovery strings from positive continuum
type-density samples. The distinguished initial mass and midpoint gap
convention are exact. The state recursion is the actual drift/impulse
recursion, so later consistency estimates concern real finite strings.
Source: the explicit recovery construction printed in Appendix C.
-/
namespace krylov.Asymptotics
noncomputable section
open Set
open krylov.Strings

/-- A physical type grid inside the prescribed continuum window. -/
theorem grid_mem {Y h : ℝ} {N k : ℕ} (hh : 0 ≤ h) (hNY : (N : ℝ) * h ≤ Y)
    (hk : k ≤ N) : (k : ℝ) * h ∈ Icc 0 Y := by
  exact ⟨mul_nonneg (Nat.cast_nonneg k) hh,
    (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hk) hh).trans hNY⟩

/-- Every edge midpoint remains in the same actual continuum window. -/
theorem midpoint_grid_mem {Y h : ℝ} {N k : ℕ} (hh : 0 ≤ h)
    (hNY : (N : ℝ) * h ≤ Y) (hk : k < N) : ((k : ℝ) + 1 / 2) * h ∈ Icc 0 Y := by
  have hkn : (k : ℝ) + 1 ≤ N := by exact_mod_cast Nat.succ_le_of_lt hk
  constructor
  · positivity
  · exact (mul_le_mul_of_nonneg_right (by linarith : (k : ℝ) + 1 / 2 ≤ N) hh).trans hNY

/-- The actual finite recovery string. `N` counts edges, and its mass at
zero remains exactly one instead of being replaced by a density sample. -/
def recoveryString (v : ℝ → ℝ) {Y h : ℝ} (hh : 0 < h) (N : ℕ)
    (hNY : (N : ℝ) * h ≤ Y) (hv : ∀ y ∈ Icc 0 Y, 0 < v y) : DiscreteString N where
  mass k := if k = 0 then 1 else h * v ((k : ℝ) * h)
  gap k := h / v (((k : ℝ) + 1 / 2) * h)
  mass_zero := by simp
  mass_pos k hk := by
    by_cases hk₀ : k = 0
    · simp [hk₀]
    · simp only [hk₀, ite_false]
      exact mul_pos hh (hv _ (grid_mem hh.le hNY hk))
  gap_pos k hk := div_pos hh (hv _ (midpoint_grid_mem hh.le hNY hk))
  robin := 0
  robin_nonneg := le_rfl

@[simp] theorem recoveryString_mass_succ (v : ℝ → ℝ) {Y h : ℝ} (hh : 0 < h) (N : ℕ)
    (hNY : (N : ℝ) * h ≤ Y) (hv : ∀ y ∈ Icc 0 Y, 0 < v y) (k : ℕ) :
    (recoveryString v hh N hNY hv).mass (k + 1) = h * v (((k : ℝ) + 1) * h) := by
  simp [recoveryString]

@[simp] theorem recoveryString_gap (v : ℝ → ℝ) {Y h : ℝ} (hh : 0 < h) (N : ℕ)
    (hNY : (N : ℝ) * h ≤ Y) (hv : ∀ y ∈ Icc 0 Y, 0 < v y) (k : ℕ) :
    (recoveryString v hh N hNY hv).gap k = h / v (((k : ℝ) + 1 / 2) * h) := rfl

/-- The actual position recurrence of the constructed recovery string. -/
theorem recoveryString_position_step (v : ℝ → ℝ) {Y h : ℝ} (hh : 0 < h) (N : ℕ)
    (hNY : (N : ℝ) * h ≤ Y) (hv : ∀ y ∈ Icc 0 Y, 0 < v y) (k : ℕ) :
    let S := recoveryString v hh N hNY hv
    S.φ (k + 1) = S.φ k + h / v (((k : ℝ) + 1 / 2) * h) * S.p k := rfl

/-- The actual post-mass slope recurrence of the recovery string. -/
theorem recoveryString_slope_step (v : ℝ → ℝ) {Y h : ℝ} (hh : 0 < h) (N : ℕ)
    (hNY : (N : ℝ) * h ≤ Y) (hv : ∀ y ∈ Icc 0 Y, 0 < v y) (k : ℕ) :
    let S := recoveryString v hh N hNY hv
    S.p (k + 1) = S.p k + h * v (((k : ℝ) + 1) * h) * S.φ (k + 1) := by
  dsimp only
  rw [DiscreteString.p_succ, recoveryString_mass_succ]

/-- The actual Christoffel energy recurrence of the recovery string. -/
theorem recoveryString_energy_step (v : ℝ → ℝ) {Y h : ℝ} (hh : 0 < h) (N : ℕ)
    (hNY : (N : ℝ) * h ≤ Y) (hv : ∀ y ∈ Icc 0 Y, 0 < v y) (k : ℕ) :
    let S := recoveryString v hh N hNY hv
    S.K (k + 1) = S.K k + h * v (((k : ℝ) + 1) * h) * S.φ (k + 1) ^ 2 := by
  dsimp only
  rw [DiscreteString.K_succ, recoveryString_mass_succ]

end
end krylov.Asymptotics
