import krylov.ContinuumControl.Potential
import Mathlib.Analysis.Real.Sqrt

/-!
Article: main_krylov, thm:value, gamma=1 terminal estimate.
Use: derive the decay of the endpoint Bellman value from the printed orbit
corridor r+1 < σ(r) ≤ 4r. Construction of that global orbit is independent.
Source: monotonicity of square roots and elementary filter limits in mathlib.
-/

namespace krylov.ContinuumControl
noncomputable section
open Filter Topology

/-- The endpoint graph corridor gives the explicit terminal majorant. -/
theorem endpoint_feedback_bound {σ : ℝ → ℝ} {r : ℝ} (hr : 1 ≤ r)
    (hlo : r + 1 ≤ σ r) (hhi : σ r ≤ 4 * r) :
    feedbackValue 1 σ r ≤ 5 / (2 * Real.sqrt (r + 1)) := by
  have hrp : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hs : 0 < σ r := lt_of_lt_of_le (by linarith : 0 < r + 1) hlo
  have ht : 0 < Real.sqrt (σ r) := Real.sqrt_pos.mpr hs
  have htr : 0 < Real.sqrt (r + 1) := Real.sqrt_pos.mpr (by linarith)
  have hsqrt : Real.sqrt (r + 1) ≤ Real.sqrt (σ r) := Real.sqrt_le_sqrt hlo
  calc
    feedbackValue 1 σ r ≤ (5 * r) / (2 * r * Real.sqrt (σ r)) := by
      unfold feedbackValue
      simp only [mul_one]
      apply div_le_div_of_nonneg_right _ (by positivity)
      linarith
    _ = 5 / (2 * Real.sqrt (σ r)) := by field_simp
    _ ≤ 5 / (2 * Real.sqrt (r + 1)) :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)

/-- The scalar terminal Bellman value tends to zero on every graph in
the endpoint corridor. In particular, no boundedness assumption on f is
silently substituted for the stronger decay needed at gamma=1. -/
theorem endpoint_feedback_tendsto_zero {σ : ℝ → ℝ}
    (hlo : ∀ r : ℝ, 1 ≤ r → r + 1 ≤ σ r)
    (hhi : ∀ r : ℝ, 1 ≤ r → σ r ≤ 4 * r) :
    Tendsto (feedbackValue 1 σ) atTop (𝓝 0) := by
  have hplus : Tendsto (fun r : ℝ ↦ r + 1) atTop atTop := tendsto_atTop_add_const_right atTop 1 tendsto_id
  have hroot := Real.tendsto_sqrt_atTop.comp hplus
  have hlim : Tendsto (fun r : ℝ ↦ 5 / (2 * Real.sqrt (r + 1))) atTop (𝓝 0) := by
    have h := (tendsto_inv_atTop_zero.comp hroot).const_mul (5 / 2 : ℝ)
    simpa only [Function.comp_def, mul_zero, zero_mul, div_eq_mul_inv, mul_inv_rev,
      mul_assoc, mul_comm, mul_left_comm] using h
  apply squeeze_zero' _ _ hlim
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
    exact (feedbackValue_pos (by norm_num) hr (by linarith [hlo r hr])).le
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
    exact endpoint_feedback_bound hr (hlo r hr) (hhi r hr)

/-- Along an endpoint feedback trajectory, r→∞ and the physical bound K≥1
already force terminal potential decay. No assumed terminal-value limit is
needed once these genuine orbit properties have been established. -/
theorem endpoint_stateValue_tendsto_zero {σ φ p K : ℝ → ℝ}
    (hlo : ∀ r : ℝ, 1 ≤ r → r + 1 ≤ σ r)
    (hhi : ∀ r : ℝ, 1 ≤ r → σ r ≤ 4 * r)
    (hr : Tendsto (fun x ↦ φ x * p x / K x) atTop atTop)
    (hK : ∀ᶠ x in atTop, 1 ≤ K x) :
    Tendsto (fun x ↦ stateValue 1 σ (φ x) (p x) (K x)) atTop (𝓝 0) := by
  have hlim := (endpoint_feedback_tendsto_zero hlo hhi).comp hr
  have hdom : ∀ᶠ x in atTop, 1 ≤ φ x * p x / K x :=
    hr.eventually (eventually_ge_atTop 1)
  apply squeeze_zero' _ _ hlim
  · filter_upwards [hK, hdom] with x hx hxr
    have hf := feedbackValue_pos (σ := σ) (by norm_num : (0 : ℝ) < 1) hxr
      (by linarith [hlo _ hxr])
    dsimp [stateValue]
    exact mul_nonneg (Real.rpow_nonneg (by linarith) _) hf.le
  · filter_upwards [hK, hdom] with x hx hxr
    have hf := feedbackValue_pos (σ := σ) (by norm_num : (0 : ℝ) < 1) hxr
      (by linarith [hlo _ hxr])
    have hinv : (K x)⁻¹ ≤ 1 := by
      simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hx
    dsimp [stateValue]
    rw [Real.rpow_neg_one]
    exact mul_le_of_le_one_left hf.le hinv

end
end krylov.ContinuumControl
