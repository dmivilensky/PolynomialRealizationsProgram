import krylov.Strings.State
import Mathlib.Analysis.BoundedVariation
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm

/-!
Article: main_krylov, apC:eq:state (regularity of the state).
Use: Derive monotonicity, compact bounded variation and right continuity of
the cumulative slope and energy against general Stieltjes mass.
Source: positive measure integration, mathlib's monotone bounded-variation
theorem and dominated convergence. Atoms are retained throughout.
-/

namespace krylov.Strings
noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal

namespace Mass

/-- The reconstructed slope is monotone for a normalized monotone position. -/
theorem slope_monotone (M : Mass) {φ : ℝ → ℝ} (hc : Continuous φ)
    (hm : Monotone φ) (h₀ : φ 0 = 1) : Monotone (integralSlope M.measure φ) := by
  intro x y hxy
  apply add_le_add_right
  apply setIntegral_mono_set (M.position_integrable hc y)
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have hp := hm ht.1.le
    rw [h₀] at hp
    exact zero_le_one.trans hp
  · exact Eventually.of_forall (fun _ ht ↦ ⟨ht.1, ht.2.trans hxy⟩)

/-- The reconstructed energy is monotone for every continuous position state. -/
theorem energy_monotone (M : Mass) {φ : ℝ → ℝ} (hc : Continuous φ) :
    Monotone (integralEnergy M.measure φ) := by
  intro x y hxy
  apply add_le_add_right
  apply setIntegral_mono_set (M.position_integrable (hc.pow 2) y)
  · exact Eventually.of_forall (fun t ↦ sq_nonneg (φ t))
  · exact Eventually.of_forall (fun _ ht ↦ ⟨ht.1, ht.2.trans hxy⟩)

/-- Monotone slopes have bounded variation on every compact window. -/
theorem slope_boundedVariationOn (M : Mass) {φ : ℝ → ℝ} (hc : Continuous φ)
    (hm : Monotone φ) (h₀ : φ 0 = 1) (a b : ℝ) :
    BoundedVariationOn (integralSlope M.measure φ) (Icc a b) := by
  have h := ((M.slope_monotone hc hm h₀).monotoneOn univ).locallyBoundedVariationOn
    a b (mem_univ a) (mem_univ b)
  simpa using h

/-- Energies have bounded variation on every compact window. -/
theorem energy_boundedVariationOn (M : Mass) {φ : ℝ → ℝ} (hc : Continuous φ)
    (a b : ℝ) : BoundedVariationOn (integralEnergy M.measure φ) (Icc a b) := by
  have h := ((M.energy_monotone hc).monotoneOn univ).locallyBoundedVariationOn
    a b (mem_univ a) (mem_univ b)
  simpa using h

/-- Cumulative mass integrals are right-continuous, including at atoms.
The domination uses one larger finite mass window; no global integrability
or absence of atoms is required. -/
theorem cumulativeIntegral_right_continuous (M : Mass) {φ : ℝ → ℝ} (hc : Continuous φ)
    (x : ℝ) : ContinuousWithinAt (fun t ↦ ∫ y in Ioc 0 t, φ y ∂M.measure) (Ici x) x := by
  have hi : Integrable ((Ioc 0 (x + 1)).indicator (fun y ↦ ‖φ y‖)) M.measure := by
    rw [integrable_indicator_iff measurableSet_Ioc]
    exact (M.position_integrable hc (x + 1)).norm
  have hF : ∀ t : ℝ, AEStronglyMeasurable ((Ioc 0 t).indicator φ) M.measure := by
    intro t
    exact (hc.measurable.indicator measurableSet_Ioc).aestronglyMeasurable
  have hbound : ∀ᶠ t in 𝓝[Ici x] x, ∀ᵐ y ∂M.measure,
      ‖(Ioc 0 t).indicator φ y‖ ≤ (Ioc 0 (x + 1)).indicator (fun u ↦ ‖φ u‖) y := by
    have ht : ∀ᶠ t in 𝓝[Ici x] x, t < x + 1 :=
      (eventually_lt_nhds (show x < x + 1 by linarith)).filter_mono nhdsWithin_le_nhds
    filter_upwards [ht] with t ht
    filter_upwards with y
    by_cases hy : y ∈ Ioc 0 t
    · have hy' : y ∈ Ioc 0 (x + 1) := ⟨hy.1, hy.2.trans ht.le⟩
      simp only [indicator_of_mem hy, indicator_of_mem hy', le_refl]
    · rw [indicator_of_notMem hy, norm_zero]
      exact indicator_nonneg (fun _ _ ↦ norm_nonneg _) _
  have hcont : ∀ᵐ y ∂M.measure, ContinuousWithinAt
      (fun t : ℝ ↦ (Ioc 0 t).indicator φ y) (Ici x) x := by
    filter_upwards with y
    by_cases hy : y ∈ Ioc 0 x
    · apply (continuousWithinAt_const (b := φ y)).congr_of_eventuallyEq
      filter_upwards [self_mem_nhdsWithin] with t ht
      exact indicator_of_mem (show y ∈ Ioc 0 t from ⟨hy.1, hy.2.trans ht⟩) φ
      exact indicator_of_mem hy φ
    · by_cases hyp : 0 < y
      · have hxy : x < y := lt_of_not_ge (fun h ↦ hy ⟨hyp, h⟩)
        apply (continuousWithinAt_const (b := (0 : ℝ))).congr_of_eventuallyEq
        have ht : ∀ᶠ t in 𝓝[Ici x] x, t < y :=
          (eventually_lt_nhds hxy).filter_mono nhdsWithin_le_nhds
        filter_upwards [ht] with t ht
        exact indicator_of_notMem (show y ∉ Ioc 0 t from fun h ↦ (not_le_of_gt ht) h.2) φ
        exact indicator_of_notMem hy φ
      · apply (continuousWithinAt_const (b := (0 : ℝ))).congr_of_eventuallyEq
        exact Eventually.of_forall (fun t ↦
          indicator_of_notMem (show y ∉ Ioc 0 t from fun h ↦ hyp h.1) φ)
        exact indicator_of_notMem hy φ
  have h := continuousWithinAt_of_dominated (Eventually.of_forall hF) hbound hi hcont
  simpa only [integral_indicator measurableSet_Ioc] using h

/-- The article's slope has the right-continuity convention of a string. -/
theorem slope_right_continuous (M : Mass) {φ : ℝ → ℝ} (hc : Continuous φ) (x : ℝ) :
    ContinuousWithinAt (integralSlope M.measure φ) (Ici x) x :=
  continuousWithinAt_const.add (M.cumulativeIntegral_right_continuous hc x)

/-- The article's energy is right-continuous even at an atom. -/
theorem energy_right_continuous (M : Mass) {φ : ℝ → ℝ} (hc : Continuous φ) (x : ℝ) :
    ContinuousWithinAt (integralEnergy M.measure φ) (Ici x) x :=
  continuousWithinAt_const.add (M.cumulativeIntegral_right_continuous (hc.pow 2) x)

/-- The actual position state is absolutely continuous on each finite window,
even when its slope jumps because the string has atoms. -/
theorem position_absolutelyContinuousOnInterval (M : Mass) (L : ℝ≥0) {φ : ℝ → ℝ}
    (hc : Continuous φ) (hm : Monotone φ) (h₀ : φ 0 = 1)
    (he : ∀ x ∈ Icc 0 (L : ℝ), φ x = 1 + ∫ t in Ioc 0 x, integralSlope M.measure φ t) :
    AbsolutelyContinuousOnInterval φ 0 (L : ℝ) := by
  have hL : (0 : ℝ) ≤ (L : ℝ) := L.property
  have hp : IntervalIntegrable (integralSlope M.measure φ) volume 0 (L : ℝ) :=
    (M.slope_monotone hc hm h₀).intervalIntegrable
  have hi := hp.absolutelyContinuousOnInterval_intervalIntegral (left_mem_uIcc :
    (0 : ℝ) ∈ uIcc 0 (L : ℝ))
  have hconst : AbsolutelyContinuousOnInterval (fun _ : ℝ ↦ (1 : ℝ)) 0 (L : ℝ) :=
    (LipschitzWith.const (1 : ℝ)).lipschitzOnWith.absolutelyContinuousOnInterval
  apply (hconst.add hi).congr
  intro x hx
  rw [uIcc_of_le hL] at hx
  change 1 + (∫ t in (0 : ℝ)..x, integralSlope M.measure φ t) = φ x
  rw [intervalIntegral.integral_of_le hx.1, he x hx]

/-- Lebesgue differentiation of the actual state integral gives `φ'=p`
almost everywhere in the physical window, without imposing smooth mass. -/
theorem position_ae_hasDerivAt (M : Mass) (L : ℝ≥0) {φ : ℝ → ℝ}
    (hc : Continuous φ) (hm : Monotone φ) (h₀ : φ 0 = 1)
    (he : ∀ x ∈ Icc 0 (L : ℝ), φ x = 1 + ∫ t in Ioc 0 x, integralSlope M.measure φ t) :
    ∀ᵐ x : ℝ, x ∈ Ioo 0 (L : ℝ) → HasDerivAt φ (integralSlope M.measure φ x) x := by
  have hL : (0 : ℝ) ≤ (L : ℝ) := L.property
  have hp : IntervalIntegrable (integralSlope M.measure φ) volume 0 (L : ℝ) :=
    (M.slope_monotone hc hm h₀).intervalIntegrable
  filter_upwards [hp.ae_hasDerivAt_integral] with x hx
  intro hxin
  have hxclosed : x ∈ uIcc 0 (L : ℝ) := by
    rw [uIcc_of_le hL]
    exact ⟨hxin.1.le, hxin.2.le⟩
  have hd := (hx hxclosed 0 left_mem_uIcc).const_add 1
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hxin.1 hxin.2] with t ht
  rw [he t ⟨ht.1.le, ht.2.le⟩, intervalIntegral.integral_of_le ht.1.le]

end Mass
end
end krylov.Strings
