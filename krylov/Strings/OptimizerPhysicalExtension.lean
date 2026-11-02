import krylov.Strings.OptimizerPhysicalState

/-!
Article: main_krylov, thm:value, actual global physical optimizer coordinates.
Use: extend the constructed physical coordinates continuously to the real line
without altering them near any physical position, including zero. This permits
the existing genuine global-mass construction and state/reward integration APIs.
Source: the real inverse function theorem and the proved unbounded physical clock.
-/

namespace krylov.Strings.OptimizerQuadratures
noncomputable section
open Set Filter MeasureTheory
open scoped Topology

/-- The physical clock covers the half-line above any one of its values. -/
theorem clock_surjOn_above {s : ℝ → ℝ} (hs : Continuous s)
    (h₁ : ∀ t ≥ 0, 1 ≤ s t) (a : ℝ) :
    SurjOn (physicalClock s) (Ici a) (Ici (physicalClock s a)) := by
  have hc : Continuous (physicalClock s) := continuous_iff_continuousAt.mpr
    (fun t ↦ (physicalClock_derivative hs t).continuousAt)
  intro x hx
  exact intermediate_value_Ici (a := a) hc.continuousOn (physicalClock_tendsto_atTop hs h₁) hx

/-- The inverse physical clock has reciprocal-speed derivative above any actual clock value. -/
theorem inverseClock_derivative_above {s : ℝ → ℝ} (hs : Continuous s)
    (hp : ∀ t, 0 < s t) (h₁ : ∀ t ≥ 0, 1 ≤ s t) {a x : ℝ}
    (hx : physicalClock s a ≤ x) :
    HasDerivAt (inverseClock s) (physicalSpeed s (inverseClock s x))⁻¹ x := by
  obtain ⟨t, _, ht⟩ := clock_surjOn_above hs h₁ a hx
  have hi : inverseClock s x = t := by
    rw [← ht]
    exact Function.leftInverse_invFun (physicalClock_strictMono hs hp).injective t
  rw [hi, ← ht]
  exact inverseClock_derivative hs hp t

/-- A fixed negative physical cutoff lies strictly before the entire physical
half-line, inside the genuine range of the actual clock. -/
def physicalCutoff (s : ℝ → ℝ) : ℝ := physicalClock s (-1)

/-- The extension cutoff lies strictly to the left of the source physical domain. -/
theorem physicalCutoff_neg {s : ℝ → ℝ} (hs : Continuous s) (hp : ∀ t, 0 < s t) :
    physicalCutoff s < 0 := by
  simpa only [physicalCutoff, physicalClock_zero] using
    physicalClock_strictMono hs hp (by norm_num : (-1 : ℝ) < 0)

/-- Continuous extension of a quadrature coordinate through its inverse clock. -/
def extendedPullback (s f : ℝ → ℝ) (x : ℝ) : ℝ :=
  f (inverseClock s (max x (physicalCutoff s)))

/-- A continuous orbit coordinate has a continuous extended inverse-clock pullback. -/
theorem extendedPullback_continuous {s f : ℝ → ℝ} (hs : Continuous s)
    (hp : ∀ t, 0 < s t) (h₁ : ∀ t ≥ 0, 1 ≤ s t) (hf : Continuous f) :
    Continuous (extendedPullback s f) := by
  have hc : ContinuousOn (fun x ↦ f (inverseClock s x)) (Ici (physicalCutoff s)) := by
    intro x hx
    have hpoint : ContinuousAt (fun y ↦ f (inverseClock s y)) x := hf.continuousAt.tendsto.comp
      (inverseClock_derivative_above hs hp h₁ hx).continuousAt.tendsto
    exact hpoint.continuousWithinAt
  apply hc.comp_continuous (continuous_id.max continuous_const)
  intro x
  change physicalCutoff s ≤ max x (physicalCutoff s)
  exact le_max_right _ _

/-- Near every source position the extension equals the true inverse-clock pullback. -/
theorem extendedPullback_eventually {s : ℝ → ℝ} (hs : Continuous s)
    (hp : ∀ t, 0 < s t) (f : ℝ → ℝ) {x : ℝ} (hx : 0 ≤ x) :
    extendedPullback s f =ᶠ[𝓝 x] fun y ↦ f (inverseClock s y) := by
  have hcut : physicalCutoff s < x := (physicalCutoff_neg hs hp).trans_le hx
  filter_upwards [Ioi_mem_nhds hcut] with y hy
  exact congrArg (fun z ↦ f (inverseClock s z)) (max_eq_left hy.le)

/-- The continuous real-line representative of the physical position quadrature. -/
def extendedPosition (s : ℝ → ℝ) : ℝ → ℝ := extendedPullback s (expPrimitive s)
/-- The continuous real-line representative of the physical slope quadrature. -/
def extendedSlope (s : ℝ → ℝ) : ℝ → ℝ := extendedPullback s Real.exp
/-- The continuous real-line representative of the physical energy quadrature. -/
def extendedEnergy (s U : ℝ → ℝ) : ℝ → ℝ := extendedPullback s (expPrimitive U)
/-- The physical square-root mass density expressed through the LV feedback quadratures. -/
def densityInOrbitTime (s : ℝ → ℝ) (t : ℝ) : ℝ :=
  Real.exp t / (expPrimitive s t * Real.sqrt (s t))
/-- The continuous real-line representative of the physical feedback density. -/
def extendedDensity (s : ℝ → ℝ) : ℝ → ℝ := extendedPullback s (densityInOrbitTime s)

/-- The density in LV coordinates is continuous for a continuous positive state. -/
theorem densityInOrbitTime_continuous {s : ℝ → ℝ} (hs : Continuous s) (hp : ∀ t, 0 < s t) :
    Continuous (densityInOrbitTime s) := by
  exact Real.continuous_exp.div ((expPrimitive_continuous hs).mul (Real.continuous_sqrt.comp hs))
    (fun t ↦ mul_ne_zero (expPrimitive_pos s t).ne' (Real.sqrt_pos.mpr (hp t)).ne')

/-- The extended physical feedback density is continuous. -/
theorem extendedDensity_continuous {s : ℝ → ℝ} (hs : Continuous s)
    (hp : ∀ t, 0 < s t) (h₁ : ∀ t ≥ 0, 1 ≤ s t) : Continuous (extendedDensity s) :=
  extendedPullback_continuous hs hp h₁ (densityInOrbitTime_continuous hs hp)

/-- All three extended physical state coordinates are continuous. -/
theorem extended_coordinates_continuous {s U : ℝ → ℝ} (hs : Continuous s) (hU : Continuous U)
    (hp : ∀ t, 0 < s t) (h₁ : ∀ t ≥ 0, 1 ≤ s t) :
    Continuous (extendedPosition s) ∧ Continuous (extendedSlope s) ∧ Continuous (extendedEnergy s U) :=
  ⟨extendedPullback_continuous hs hp h₁ (expPrimitive_continuous hs),
    extendedPullback_continuous hs hp h₁ Real.continuous_exp,
    extendedPullback_continuous hs hp h₁ (expPrimitive_continuous hU)⟩

/-- Extended and genuine physical coordinates agree on the entire source half-line. -/
theorem extended_coordinates_eq {s U : ℝ → ℝ} (hs : Continuous s)
    (hp : ∀ t, 0 < s t) {x : ℝ} (hx : 0 ≤ x) :
    extendedPosition s x = physicalPosition s x ∧ extendedSlope s x = physicalSlope s x ∧
      extendedEnergy s U x = physicalEnergy s U x ∧ extendedDensity s x = physicalDensity s x := by
  exact ⟨(extendedPullback_eventually hs hp (expPrimitive s) hx).self_of_nhds,
    (extendedPullback_eventually hs hp Real.exp hx).self_of_nhds,
    (extendedPullback_eventually hs hp (expPrimitive U) hx).self_of_nhds,
    (extendedPullback_eventually hs hp (densityInOrbitTime s) hx).self_of_nhds⟩

/-- The actual global continuous coordinate extensions obey the string ODE at
every nonnegative physical point, including the distinguished left endpoint. -/
theorem extended_smoothStringAt {s U : ℝ → ℝ} (hs : Continuous s) (hU : Continuous U)
    (hp : ∀ t, 0 < s t) (h₁ : ∀ t ≥ 0, 1 ≤ s t) (hU₀ : U 0 = 1)
    (hode : ∀ t > 0, HasDerivAt U (U t * (s t + 1 - U t)) t)
    {x : ℝ} (hx : 0 ≤ x) :
    krylov.ContinuumControl.SmoothStringAt (extendedPosition s) (extendedSlope s)
      (extendedEnergy s U) (extendedDensity s) x := by
  have hstate := physical_smoothStringAt hs hU hp h₁ hU₀ hode hx
  obtain ⟨hφ, hP, hK, hv⟩ := extended_coordinates_eq (U := U) hs hp hx
  refine ⟨hφ.symm ▸ hstate.φ_pos, hP.symm ▸ hstate.p_pos, hK.symm ▸ hstate.K_pos, ?_, ?_, ?_⟩
  · rw [hP]
    exact hstate.φ_deriv.congr_of_eventuallyEq (extendedPullback_eventually hs hp (expPrimitive s) hx)
  · rw [hφ, hv]
    exact hstate.p_deriv.congr_of_eventuallyEq (extendedPullback_eventually hs hp Real.exp hx)
  · rw [hφ, hv]
    exact hstate.K_deriv.congr_of_eventuallyEq (extendedPullback_eventually hs hp (expPrimitive U) hx)

end
end krylov.Strings.OptimizerQuadratures
