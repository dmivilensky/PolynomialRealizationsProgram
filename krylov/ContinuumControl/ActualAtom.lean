import krylov.Strings.AtomicState
import krylov.ContinuumControl.Impulse

/-!
Article: main_krylov, apC:lem:fund, atom loss for the actual string state.
Use: apply the finite-impulse identity to genuine left limits of the
measure-driven slope and energy, with their actual atom mass.
Source: dominated convergence and splitting a singleton from the mass integral.
-/

namespace krylov.ContinuumControl
noncomputable section
open Set MeasureTheory krylov.Strings

/-- The actual pre-atom state remains in the positive physical domain.
Earlier atoms and singular continuous mass are all included. -/
theorem actual_left_state_pos (M : Mass) {φ : ℝ → ℝ}
    (hc : Continuous φ) (hm : Monotone φ) (h₀ : φ 0 = 1) {x : ℝ} (hx : 0 < x) :
    0 < φ x ∧ 0 < Function.leftLim (integralSlope M.measure φ) x ∧
      0 < Function.leftLim (integralEnergy M.measure φ) x := by
  have hφ : 1 ≤ φ x := by simpa [h₀] using hm hx.le
  rw [M.slope_leftLim hc x, M.energy_leftLim hc x]
  have hp : 0 ≤ ∫ y in Ioo 0 x, φ y ∂M.measure := by
    apply setIntegral_nonneg measurableSet_Ioo
    intro y hy
    have hyφ : 1 ≤ φ y := by simpa [h₀] using hm hy.1.le
    linarith
  have hK : 0 ≤ ∫ y in Ioo 0 x, φ y ^ 2 ∂M.measure :=
    setIntegral_nonneg measurableSet_Ioo (fun y _ ↦ sq_nonneg (φ y))
  exact ⟨by linarith, by linarith, by linarith⟩

/-- Exact potential drop for a positive-position atom of the actual
string measure. None of the impulse coordinates are supplied independently. -/
theorem actual_atom_potential_decrement (M : Mass) {γ : ℝ} {σ φ : ℝ → ℝ}
    (hγ : γ ≠ 0) (hc : Continuous φ) (hm : Monotone φ) (h₀ : φ 0 = 1)
    {x : ℝ} (hx : 0 < x)
    (hgraph : ∀ u ∈ Icc 0 (M.measure.real {x}),
      FeedbackGraphAt γ σ
        (φ x * (Function.leftLim (integralSlope M.measure φ) x + u * φ x) /
          (Function.leftLim (integralEnergy M.measure φ) x + u * φ x ^ 2))) :
    stateValue γ σ (φ x) (Function.leftLim (integralSlope M.measure φ) x)
        (Function.leftLim (integralEnergy M.measure φ) x) -
      stateValue γ σ (φ x) (integralSlope M.measure φ x) (integralEnergy M.measure φ x) =
      impulseLoss γ σ (φ x) (Function.leftLim (integralSlope M.measure φ) x)
        (Function.leftLim (integralEnergy M.measure φ) x) (M.measure.real {x}) := by
  obtain ⟨hφ, hp, hK⟩ := actual_left_state_pos M hc hm h₀ hx
  rw [M.slope_atom_update hc hx, M.energy_atom_update hc hx]
  exact impulse_potential_decrement hγ hφ hp hK ENNReal.toReal_nonneg hgraph

/-- Every actual nonzero atom has a strictly positive loss, so equality
in the final general BV identity will exclude all positive-position atoms. -/
theorem actual_atom_loss_pos (M : Mass) {γ : ℝ} {σ φ : ℝ → ℝ}
    (hc : Continuous φ) (hm : Monotone φ) (h₀ : φ 0 = 1)
    {x : ℝ} (hx : 0 < x) (hAtom : 0 < M.measure.real {x})
    (hgraph : ∀ u ∈ Icc 0 (M.measure.real {x}),
      FeedbackGraphAt γ σ
        (φ x * (Function.leftLim (integralSlope M.measure φ) x + u * φ x) /
          (Function.leftLim (integralEnergy M.measure φ) x + u * φ x ^ 2))) :
    0 < impulseLoss γ σ (φ x) (Function.leftLim (integralSlope M.measure φ) x)
      (Function.leftLim (integralEnergy M.measure φ) x) (M.measure.real {x}) := by
  obtain ⟨hφ, hp, hK⟩ := actual_left_state_pos M hc hm h₀ hx
  exact impulseLoss_pos hφ hp hK hAtom hgraph

end
end krylov.ContinuumControl
