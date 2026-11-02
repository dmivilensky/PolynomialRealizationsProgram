import krylov.Strings.Mass
import krylov.Strings.FeedbackMeasureInvariant
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
Article: main_krylov, apC:eq:state, general string invariant.
Use: discharge integrability in the measure-based invariant for actual string
mass and a continuous monotone physical position state. Atoms and singular
continuous mass are both retained.
Source: compact-window integrability from mathlib; `Mass.measure` is locally finite.
-/

namespace krylov.Strings
noncomputable section
open Set MeasureTheory

/-- Continuous physical positions and their squares are integrable on every
finite string window. This derives the analytic side conditions of the ratio
invariant from actual string data. -/
theorem mass_window_position_integrable (M : Mass) {φ : ℝ → ℝ} {x : ℝ}
    (hc : ContinuousOn φ (Icc 0 x)) :
    IntegrableOn φ (Ioc 0 x) M.measure ∧
    IntegrableOn (fun t ↦ φ t ^ 2) (Ioc 0 x) M.measure := by
  have : IsLocallyFiniteMeasure M.measure := by
    dsimp [Mass.measure]
    infer_instance
  exact ⟨hc.integrableOn_Icc.mono_set Ioc_subset_Icc_self,
    (hc.pow 2).integrableOn_Icc.mono_set Ioc_subset_Icc_self⟩

/-- The true string measure gives φp≥K whenever the position state is
continuous, nondecreasing and initialized at one. -/
theorem mass_state_excess_nonneg (M : Mass) {φ : ℝ → ℝ} {x : ℝ}
    (hx : 0 ≤ x) (hφ : φ 0 = 1) (hc : ContinuousOn φ (Icc 0 x))
    (hm : MonotoneOn φ (Icc 0 x)) :
    0 ≤ φ x * integralSlope M.measure φ x - integralEnergy M.measure φ x := by
  obtain ⟨hi, hi₂⟩ := mass_window_position_integrable M hc
  exact integral_state_excess_nonneg hx hφ.ge hm hi hi₂

/-- General-mass state ratio, with no density or smoothness assumption on M. -/
theorem mass_state_ratio_ge_one (M : Mass) {φ : ℝ → ℝ} {x : ℝ}
    (hx : 0 ≤ x) (hφ : φ 0 = 1) (hc : ContinuousOn φ (Icc 0 x))
    (hm : MonotoneOn φ (Icc 0 x)) :
    1 ≤ stateRatio (φ x) (integralSlope M.measure φ x) (integralEnergy M.measure φ x) := by
  obtain ⟨hi, hi₂⟩ := mass_window_position_integrable M hc
  exact integral_state_ratio_ge_one hx hφ.ge hm hi hi₂

end
end krylov.Strings
