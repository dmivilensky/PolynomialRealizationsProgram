import krylov.Strings.StateRegularity
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
Article: main_krylov, apC:eq:state and apC:lem:fund, actual left states.
Use: identify left limits of the physical cumulative integrals before applying
the finite-impulse potential formula. No atom-free or smooth-mass assumption.
Source: dominated convergence with a fixed finite mass window.
-/

namespace krylov.Strings
noncomputable section
open Set Filter MeasureTheory
open scoped Topology

namespace Mass

/-- The left limit excludes the current atom, unlike the right-continuous
physical state. -/
theorem cumulativeIntegral_tendsto_left (M : Mass) {φ : ℝ → ℝ} (hc : Continuous φ)
    (x : ℝ) :
    Tendsto (fun t ↦ ∫ y in Ioc 0 t, φ y ∂M.measure) (𝓝[<] x)
      (𝓝 (∫ y in Ioo 0 x, φ y ∂M.measure)) := by
  have hi : Integrable ((Ioc 0 x).indicator (fun y ↦ ‖φ y‖)) M.measure := by
    rw [integrable_indicator_iff measurableSet_Ioc]
    exact (M.position_integrable hc x).norm
  have hF : ∀ t : ℝ, AEStronglyMeasurable ((Ioc 0 t).indicator φ) M.measure :=
    fun _ ↦ (hc.measurable.indicator measurableSet_Ioc).aestronglyMeasurable
  have hb : ∀ᶠ t in 𝓝[<] x, ∀ᵐ y ∂M.measure,
      ‖(Ioc 0 t).indicator φ y‖ ≤ (Ioc 0 x).indicator (fun u ↦ ‖φ u‖) y := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    filter_upwards with y
    by_cases hy : y ∈ Ioc 0 t
    · have hyx : y ∈ Ioc 0 x := ⟨hy.1, hy.2.trans ht.le⟩
      simp only [indicator_of_mem hy, indicator_of_mem hyx, le_refl]
    · rw [indicator_of_notMem hy, norm_zero]
      exact indicator_nonneg (fun _ _ ↦ norm_nonneg _) _
  have hl : ∀ᵐ y ∂M.measure, Tendsto (fun t : ℝ ↦ (Ioc 0 t).indicator φ y)
      (𝓝[<] x) (𝓝 ((Ioo 0 x).indicator φ y)) := by
    filter_upwards with y
    by_cases hy : y ∈ Ioo 0 x
    · rw [indicator_of_mem hy]
      apply tendsto_const_nhds.congr'
      have ht : ∀ᶠ t in 𝓝[<] x, y < t :=
        (eventually_gt_nhds hy.2).filter_mono nhdsWithin_le_nhds
      filter_upwards [ht] with t ht
      exact (indicator_of_mem (show y ∈ Ioc 0 t from ⟨hy.1, ht.le⟩) φ).symm
    · rw [indicator_of_notMem hy]
      apply tendsto_const_nhds.congr'
      filter_upwards [self_mem_nhdsWithin] with t ht
      have hyn : y ∉ Ioc 0 t := by
        intro hyt
        exact hy ⟨hyt.1, hyt.2.trans_lt ht⟩
      exact (indicator_of_notMem hyn φ).symm
  have h := tendsto_integral_filter_of_dominated_convergence _
    (Eventually.of_forall hF) hb hi hl
  simpa only [integral_indicator measurableSet_Ioc, integral_indicator measurableSet_Ioo] using h

/-- Actual pre-atom slope, expressed by the open-right integral. -/
theorem slope_leftLim (M : Mass) {φ : ℝ → ℝ} (hc : Continuous φ) (x : ℝ) :
    Function.leftLim (integralSlope M.measure φ) x =
      1 + ∫ y in Ioo 0 x, φ y ∂M.measure := by
  apply leftLim_eq_of_tendsto
  exact tendsto_const_nhds.add (M.cumulativeIntegral_tendsto_left hc x)

/-- Actual pre-atom energy, with all earlier atoms retained. -/
theorem energy_leftLim (M : Mass) {φ : ℝ → ℝ} (hc : Continuous φ) (x : ℝ) :
    Function.leftLim (integralEnergy M.measure φ) x =
      1 + ∫ y in Ioo 0 x, φ y ^ 2 ∂M.measure := by
  apply leftLim_eq_of_tendsto
  exact tendsto_const_nhds.add (M.cumulativeIntegral_tendsto_left (hc.pow 2) x)

/-- Splitting off a positive-position atom preserves all earlier mass. -/
theorem cumulativeIntegral_atom (M : Mass) {φ : ℝ → ℝ} (hc : Continuous φ)
    {x : ℝ} (hx : 0 < x) :
    (∫ y in Ioc 0 x, φ y ∂M.measure) =
      (∫ y in Ioo 0 x, φ y ∂M.measure) + M.measure.real {x} * φ x := by
  have hi := M.position_integrable hc x
  have hunion : Ioo (0 : ℝ) x ∪ {x} = Ioc 0 x := by
    ext y
    simp only [mem_union, mem_Ioo, mem_singleton_iff, mem_Ioc]
    constructor
    · rintro (⟨hy₀, hyx⟩ | rfl)
      · exact ⟨hy₀, hyx.le⟩
      · exact ⟨hx, le_rfl⟩
    · intro hy
      rcases lt_or_eq_of_le hy.2 with hlt | heq
      · exact Or.inl ⟨hy.1, hlt⟩
      · exact Or.inr heq
  have hdis : Disjoint (Ioo (0 : ℝ) x) {x} := by simp
  rw [← hunion, setIntegral_union hdis (measurableSet_singleton x)
    (hi.mono_set Ioo_subset_Ioc_self)
    (hi.mono_set (by intro y hy; simpa [mem_singleton_iff.mp hy] using (show x ∈ Ioc 0 x from ⟨hx, le_rfl⟩))),
    integral_singleton, smul_eq_mul]

/-- The true right-continuous slope is exactly the impulse update of its
left limit. The initial atom is excluded by x>0. -/
theorem slope_atom_update (M : Mass) {φ : ℝ → ℝ} (hc : Continuous φ)
    {x : ℝ} (hx : 0 < x) :
    integralSlope M.measure φ x = Function.leftLim (integralSlope M.measure φ) x +
      M.measure.real {x} * φ x := by
  rw [M.slope_leftLim hc x]
  dsimp [integralSlope]
  rw [M.cumulativeIntegral_atom hc hx]
  ring

/-- The energy uses the same actual atom and the same left state. -/
theorem energy_atom_update (M : Mass) {φ : ℝ → ℝ} (hc : Continuous φ)
    {x : ℝ} (hx : 0 < x) :
    integralEnergy M.measure φ x = Function.leftLim (integralEnergy M.measure φ) x +
      M.measure.real {x} * φ x ^ 2 := by
  rw [M.energy_leftLim hc x]
  dsimp [integralEnergy]
  have h := M.cumulativeIntegral_atom (hc.pow 2) hx
  simp only [Pi.pow_apply] at h
  rw [h]
  ring

end Mass
end
end krylov.Strings
