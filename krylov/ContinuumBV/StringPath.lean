import krylov.ContinuumBV.PotentialAtoms
import krylov.Strings.StateRegularity
import krylov.ContinuumControl.ActualAtom
import Mathlib.Topology.Order.ProjIcc

/-!
Article: main_krylov, apC:lem:fund, compact BV control for the actual string.
Use: derive bounded variation of the three actual measure-driven coordinates
and of their nonlinear Bellman potential. The compact state domain includes
the invariant K ≤ φp, so it works also for the gamma=1 graph defined near r≥1.
Source: positivity and monotonicity of the actual integral state, compact order
intervals and the C¹ composition results in `ContinuumBV.Composition`.
-/

namespace krylov.ContinuumBV
noncomputable section
open Set Filter MeasureTheory
open krylov.Strings
open scoped Topology NNReal

/-- Physical time clipped to one compact window. -/
def clipTime (L : ℝ≥0) (x : ℝ) : ℝ := projIcc 0 (L : ℝ) L.property x

/-- Clipping preserves each physical point in the selected window. -/
theorem clipTime_of_mem (L : ℝ≥0) {x : ℝ} (hx : x ∈ Icc 0 (L : ℝ)) :
    clipTime L x = x :=
  congrArg Subtype.val (projIcc_of_mem L.property hx)

/-- Before a positive point of the compact window, clipping is eventually
the identity, including when the point is the window's right endpoint. -/
theorem clipTime_eventually_left (L : ℝ≥0) {x : ℝ} (hx : 0 < x) (hxL : x ≤ L) :
    clipTime L =ᶠ[𝓝[<] x] id := by
  have hpos : ∀ᶠ t in 𝓝[<] x, 0 < t :=
    (eventually_gt_nhds hx).filter_mono nhdsWithin_le_nhds
  filter_upwards [hpos, self_mem_nhdsWithin] with t ht htx
  exact clipTime_of_mem L ⟨ht.le, htx.le.trans hxL⟩

/-- Right-continuous coordinates retain their right values after clipping,
including the rightmost atom at the compact endpoint. -/
theorem rightLim_clipped {F : Type*} [TopologicalSpace F] [T2Space F]
    {f : ℝ → F} (L : ℝ≥0) {x : ℝ} (hx : x ∈ Icc 0 (L : ℝ))
    (hf : ContinuousWithinAt f (Ici x) x) :
    Function.rightLim (fun t => f (clipTime L t)) x = f x := by
  have hclip : Continuous (clipTime L) := continuous_subtype_val.comp continuous_projIcc
  have hmaps : MapsTo (clipTime L) (Ici x) (Ici x) := by
    intro t ht
    rw [← clipTime_of_mem L hx]
    exact monotone_projIcc L.property ht
  have hc := hf.comp_of_eq hclip.continuousAt.continuousWithinAt hmaps
    (clipTime_of_mem L hx)
  simpa only [Function.comp_def, clipTime_of_mem L hx] using hc.rightLim_eq

/-- Left state limits are unchanged by compact clipping at positive points. -/
theorem leftLim_clipped {F : Type*} [TopologicalSpace F] [T2Space F]
    {f : ℝ → F} {l : F} (L : ℝ≥0) {x : ℝ} (hx : 0 < x) (hxL : x ≤ L)
    (hf : Tendsto f (𝓝[<] x) (𝓝 l)) :
    Function.leftLim (fun t => f (clipTime L t)) x = l := by
  apply leftLim_eq_of_tendsto
  apply hf.congr'
  filter_upwards [clipTime_eventually_left L hx hxL] with t ht
  simpa only [id_eq] using congrArg f ht.symm

/-- A clipped monotone scalar coordinate is globally BV. -/
theorem boundedVariation_clipped {f : ℝ → ℝ} (hf : Monotone f) (L : ℝ≥0) :
    BoundedVariationOn (fun x => f (clipTime L x)) univ := by
  have hm : Monotone (fun x => f (clipTime L x)) := by
    intro x y hxy
    exact hf (monotone_projIcc L.property hxy)
  apply (hm.monotoneOn univ).boundedVariationOn (C := |f 0| + |f L|)
  intro x _hx
  have hx := (projIcc 0 (L : ℝ) L.property x).property
  have hlo := hf hx.1
  have hhi := hf hx.2
  change |f (clipTime L x)| ≤ _
  apply abs_le.2
  constructor
  · have hl := neg_abs_le (f 0)
    have hh := abs_nonneg (f L)
    dsimp only [clipTime]
    linarith
  · have hh := le_abs_self (f L)
    have hl := abs_nonneg (f 0)
    dsimp only [clipTime]
    linarith

/-- The genuine three-coordinate physical state, extended constantly outside
the selected window solely to use the global BV Stieltjes API. -/
def clippedState (M : Mass) (φ : ℝ → ℝ) (L : ℝ≥0) (x : ℝ) : PotentialState :=
  (φ (clipTime L x), integralSlope M.measure φ (clipTime L x),
    integralEnergy M.measure φ (clipTime L x))

/-- Actual pre-atom product state of the compact BV path. -/
theorem clippedState_leftLim (M : Mass) {φ : ℝ → ℝ}
    (hc : Continuous φ) (hm : Monotone φ) (h₀ : φ 0 = 1)
    (L : ℝ≥0) {x : ℝ} (hx : 0 < x) (hxL : x ≤ L) :
    Function.leftLim (clippedState M φ L) x =
      (φ x, Function.leftLim (integralSlope M.measure φ) x,
        Function.leftLim (integralEnergy M.measure φ) x) := by
  apply leftLim_clipped
    (f := fun t => (φ t, integralSlope M.measure φ t, integralEnergy M.measure φ t)) L hx hxL
  simpa only [nhds_prod_eq] using
    (((hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).prodMk
      (((M.slope_monotone hc hm h₀).tendsto_leftLim x).prodMk
        ((M.energy_monotone hc).tendsto_leftLim x))))

/-- Actual post-atom product state, with the endpoint atom included. -/
theorem clippedState_rightLim (M : Mass) {φ : ℝ → ℝ} (hc : Continuous φ)
    (L : ℝ≥0) {x : ℝ} (hx : x ∈ Icc 0 (L : ℝ)) :
    Function.rightLim (clippedState M φ L) x =
      (φ x, integralSlope M.measure φ x, integralEnergy M.measure φ x) := by
  exact rightLim_clipped L hx
    (hc.continuousAt.continuousWithinAt.prodMk
      ((M.slope_right_continuous hc x).prodMk (M.energy_right_continuous hc x)))

/-- Actual arbitrary-measure states have BV after compact clipping. -/
theorem boundedVariation_clippedState (M : Mass) {φ : ℝ → ℝ}
    (hc : Continuous φ) (hm : Monotone φ) (h₀ : φ 0 = 1) (L : ℝ≥0) :
    BoundedVariationOn (clippedState M φ L) univ :=
  boundedVariation_prod_mk (boundedVariation_clipped hm L)
    (boundedVariation_prod_mk (boundedVariation_clipped (M.slope_monotone hc hm h₀) L)
      (boundedVariation_clipped (M.energy_monotone hc) L))

/-- The positive compact box of physical coordinates intersected with the
actual Bellman-domain invariant. This intersection need not be convex. -/
def compactStateDomain (M : Mass) (φ : ℝ → ℝ) (L : ℝ≥0) : Set PotentialState :=
  (Icc 1 (φ L) ×ˢ (Icc 1 (integralSlope M.measure φ L) ×ˢ
    Icc 1 (integralEnergy M.measure φ L))) ∩ {w | w.2.2 ≤ w.1 * w.2.1}

/-- The nonlinear invariant cuts out a closed subset of the compact box. -/
theorem isCompact_compactStateDomain (M : Mass) (φ : ℝ → ℝ) (L : ℝ≥0) :
    IsCompact (compactStateDomain M φ L) := by
  apply (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)).inter_right
  exact isClosed_le (by fun_prop) (by fun_prop)

/-- The genuine state range lies in this compact positive invariant domain;
no smoothness or absence of atoms of the mass is imposed. -/
theorem clippedState_mem (M : Mass) {φ : ℝ → ℝ}
    (hc : Continuous φ) (hm : Monotone φ) (h₀ : φ 0 = 1) (L : ℝ≥0) (x : ℝ) :
    clippedState M φ L x ∈ compactStateDomain M φ L := by
  have ht := (projIcc 0 (L : ℝ) L.property x).property
  have hφlo : 1 ≤ φ (clipTime L x) := by
    rw [← h₀]
    exact hm ht.1
  have hφhi := hm ht.2
  have hplo := M.slope_one_le hm h₀ (clipTime L x)
  have hphi := M.slope_monotone hc hm h₀ ht.2
  have hKlo := integralEnergy_one_le M.measure φ (clipTime L x)
  have hKhi := M.energy_monotone hc ht.2
  have hexcess := integral_state_excess_nonneg ht.1 (le_of_eq h₀.symm) (hm.monotoneOn _)
    (M.position_integrable hc (clipTime L x))
    (M.position_integrable (hc.pow 2) (clipTime L x))
  exact ⟨⟨⟨hφlo, hφhi⟩, ⟨⟨hplo, hphi⟩, ⟨hKlo, hKhi⟩⟩⟩, sub_nonneg.1 hexcess⟩

/-- Every point of the compact domain is positive and has ratio at least one. -/
theorem compactStateDomain_positive_ratio (M : Mass) (φ : ℝ → ℝ) (L : ℝ≥0)
    {w : PotentialState} (hw : w ∈ compactStateDomain M φ L) :
    0 < w.1 ∧ 0 < w.2.1 ∧ 0 < w.2.2 ∧ 1 ≤ w.1 * w.2.1 / w.2.2 := by
  have hφ : 0 < w.1 := zero_lt_one.trans_le hw.1.1.1
  have hp : 0 < w.2.1 := zero_lt_one.trans_le hw.1.2.1.1
  have hK : 0 < w.2.2 := zero_lt_one.trans_le hw.1.2.2.1
  exact ⟨hφ, hp, hK, (le_div_iff₀ hK).2 (by simpa using hw.2)⟩

/-- BV of the actual nonlinear potential follows from the source's genuine
graph regularity on r≥1. This also covers general singular and atomic mass. -/
theorem boundedVariation_actual_potential (M : Mass) {φ : ℝ → ℝ}
    (hc : Continuous φ) (hm : Monotone φ) (h₀ : φ 0 = 1) (L : ℝ≥0)
    {γ : ℝ} {σ : ℝ → ℝ} (hγ : γ ≠ 0)
    (hσ : ∀ r, 1 ≤ r → ContDiffAt ℝ 1 σ r)
    (hσpos : ∀ r, 1 ≤ r → 0 < σ r) :
    BoundedVariationOn (statePotential γ σ ∘ clippedState M φ L) univ := by
  apply boundedVariation_statePotential hγ (boundedVariation_clippedState M hc hm h₀ L)
    (isCompact_compactStateDomain M φ L) (fun x _ => clippedState_mem M hc hm h₀ L x)
  · intro w hw
    obtain ⟨hφ, hp, hK, _hr⟩ := compactStateDomain_positive_ratio M φ L hw
    exact ⟨hφ, hp, hK⟩
  · intro w hw
    exact hσ _ (compactStateDomain_positive_ratio M φ L hw).2.2.2
  · intro w hw
    exact hσpos _ (compactStateDomain_positive_ratio M φ L hw).2.2.2

end
end krylov.ContinuumBV
