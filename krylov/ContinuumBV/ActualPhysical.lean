import krylov.ContinuumBV.ActualContinuous
import krylov.ContinuumBV.StateIncrements
import krylov.ContinuumBV.DensitySubstitution

/-!
Article: main_krylov, apC:lem:fund, actual continuous physical mass.
Use: turn the nonlinear BV chain identity into its two physical integrals
against dx and dM, using the actual state equations and Fréchet coefficients.
No density of dM with respect to dx is assumed; singular continuous mass remains.
Source: actual interval increments and the proved continuous-coefficient substitution.
-/

namespace krylov.ContinuumBV
noncomputable section
open Set Filter MeasureTheory
open krylov.Strings krylov.ContinuumControl
open scoped Topology NNReal

/-- The positive drift cost in the physical potential decrement. -/
def driftCost (M : Mass) (γ : ℝ) (σ φ : ℝ → ℝ) (x : ℝ) : ℝ :=
  (integralEnergy M.measure φ x) ^ (-γ) * integralSlope M.measure φ x /
    (φ x * Real.sqrt (σ (φ x * integralSlope M.measure φ x / integralEnergy M.measure φ x)))

/-- The positive cost per unit mass in the physical potential decrement. -/
def massCost (M : Mass) (γ : ℝ) (σ φ : ℝ → ℝ) (x : ℝ) : ℝ :=
  massLossRate γ σ (φ x) (integralSlope M.measure φ x) (integralEnergy M.measure φ x)

/-- Continuous operator coefficients act integrably on an actual integrable
density in a compact physical window. -/
theorem coefficient_action_integrable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [CompleteSpace V] {μ : Measure ℝ} {h : ℝ → V} {c : ℝ → V →L[ℝ] ℝ}
    {a b : ℝ} (hc : Continuous c) (hi : IntegrableOn h (Ioc a b) μ) :
    IntegrableOn (fun x => c x (h x)) (Ioc a b) μ := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hc.continuousOn
  apply (hi.norm.const_mul C).mono'
  · exact derivativePairing.aestronglyMeasurable_comp₂ hc.aestronglyMeasurable hi.aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact (c x).le_opNorm (h x) |>.trans
      (mul_le_mul_of_nonneg_right (hC x (Ioc_subset_Icc_self hx)) (norm_nonneg _))

/-- Physical integral form of the actual BV chain identity on an atom-free
window, allowing arbitrary singular continuous mass. The entire state measure
is identified through its genuine interval increments before substitution. -/
theorem actual_continuous_physical_identity (M : Mass) {φ : ℝ → ℝ}
    (hc : Continuous φ) (hm : Monotone φ) (h₀ : φ 0 = 1) (L : ℝ≥0)
    (he : ∀ x ∈ Icc 0 (L : ℝ), φ x = 1 + ∫ t in Ioc 0 x, integralSlope M.measure φ t)
    (hAtom : ∀ x ∈ Ioc 0 (L : ℝ), M.measure {x} = 0)
    {γ : ℝ} {σ : ℝ → ℝ} (hγ : γ ≠ 0)
    (hσ : ∀ r, 1 ≤ r → ContDiffAt ℝ 1 σ r)
    (hgraph : ∀ r, 1 ≤ r → FeedbackGraphAt γ σ r) :
    statePotential γ σ (clippedState M φ L 0) - statePotential γ σ (clippedState M φ L L) =
      1 / 2 * (∫ x in Ioc 0 (L : ℝ), driftCost M γ σ φ x) +
        1 / 2 * (∫ x in Ioc 0 (L : ℝ), massCost M γ σ φ x ∂M.measure) := by
  let hz := boundedVariation_clippedState M hc hm h₀ L
  let ν := hz.vectorMeasure.restrict (Ioc 0 (L : ℝ))
  let c : ℝ → PotentialState →L[ℝ] ℝ :=
    fun x => fderiv ℝ (statePotential γ σ) (clippedState M φ L x)
  have hreg : ∀ w ∈ compactStateDomain M φ L, ContDiffAt ℝ 1 (statePotential γ σ) w := by
    intro w hw
    obtain ⟨hφ, hp, hK, hr⟩ := compactStateDomain_positive_ratio M φ L hw
    exact contDiffAt_statePotential hγ hφ.ne' hp.ne' hK.ne' (hσ _ hr) (hgraph _ hr).positive
  have hcc : Continuous c := by
    apply continuous_iff_continuousAt.2
    intro x
    exact ((hreg _ (clippedState_mem M hc hm h₀ L x)).continuousAt_fderiv (by norm_num)).comp
      (continuous_clippedState_of_no_atoms M hc hm h₀ L hAtom).continuousAt
  have hiν : ν.Integrable c := by
    change Integrable c (hz.vectorMeasure.restrict (Ioc 0 (L : ℝ))).variation
    rw [VectorMeasure.variation_restrict measurableSet_Ioc]
    exact hcc.integrableOn_Ioc
  have hν : ∀ᵐ x ∂ν.variation, x ∈ Ioc 0 (L : ℝ) := by
    change ∀ᵐ x ∂(hz.vectorMeasure.restrict (Ioc 0 (L : ℝ))).variation, _
    rw [VectorMeasure.variation_restrict measurableSet_Ioc]
    exact ae_restrict_mem measurableSet_Ioc
  have hD := driftDensity_integrable M hc hm h₀ 0 L
  have hM := massDensity_integrable M hc 0 L
  have hcD := coefficient_action_integrable hcc hD
  have hcM := coefficient_action_integrable hcc hM
  have hcell : ∀ u v, 0 ≤ u → u ≤ v → v ≤ (L : ℝ) →
      ν (Ioc u v) = (∫ x in Ioc u v, driftDensity M φ x ∂volume.restrict (Ioc 0 (L : ℝ))) +
        (∫ x in Ioc u v, massDensity φ x ∂M.measure.restrict (Ioc 0 (L : ℝ))) := by
    intro u v hu huv hv
    have hus : u ∈ Icc 0 (L : ℝ) := ⟨hu, huv.trans hv⟩
    have hvs : v ∈ Icc 0 (L : ℝ) := ⟨hu.trans huv, hv⟩
    have hsub : Ioc u v ⊆ Ioc (0 : ℝ) L := Ioc_subset_Ioc hu hv
    change (hz.vectorMeasure.restrict (Ioc 0 (L : ℝ))) (Ioc u v) = _
    rw [VectorMeasure.restrict_apply _ measurableSet_Ioc measurableSet_Ioc,
      inter_eq_left.2 hsub, hz.vectorMeasure_Ioc huv,
      clippedState_rightLim M hc L hvs, clippedState_rightLim M hc L hus]
    simpa only [Measure.restrict_restrict measurableSet_Ioc, inter_eq_left.2 hsub, rawState] using
      rawState_increment M hc hm h₀ L he hus hvs huv
  have hsplit := integral_eq_two_density_integrals L.property ν
    (volume.restrict (Ioc 0 (L : ℝ))) (M.measure.restrict (Ioc 0 (L : ℝ)))
    (driftDensity M φ) (massDensity φ) hcc.continuousOn hν
    (ae_restrict_mem measurableSet_Ioc) (ae_restrict_mem measurableSet_Ioc)
    hiν hD hM hcD hcM hcell
  have hchain := actual_continuous_potential_chain M hc hm h₀ L hAtom hγ hσ
    (fun r hr => (hgraph r hr).positive)
  have heqD : (∫ x in Ioc 0 (L : ℝ), c x (driftDensity M φ x)) =
      -1 / 2 * (∫ x in Ioc 0 (L : ℝ), driftCost M γ σ φ x) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro x hx
    have hdom := clippedState_mem M hc hm h₀ L x
    have hp := compactStateDomain_positive_ratio M φ L hdom
    have hd := fderiv_statePotential_drift hγ hp.1 hp.2.1 hp.2.2.1
      (hσ _ hp.2.2.2) (hgraph _ hp.2.2.2)
    simp only [c, driftDirection, clippedState, clipTime_of_mem L (Ioc_subset_Icc_self hx),
      driftDensity, driftCost, mul_div_assoc] at hd ⊢
    linear_combination hd
  have heqM : (∫ x in Ioc 0 (L : ℝ), c x (massDensity φ x) ∂M.measure) =
      -1 / 2 * (∫ x in Ioc 0 (L : ℝ), massCost M γ σ φ x ∂M.measure) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro x hx
    have hdom := clippedState_mem M hc hm h₀ L x
    have hp := compactStateDomain_positive_ratio M φ L hdom
    have hd := fderiv_statePotential_mass hγ hp.1 hp.2.1 hp.2.2.1
      (hσ _ hp.2.2.2) (hgraph _ hp.2.2.2)
    simp only [c, massDirection, clippedState, clipTime_of_mem L (Ioc_subset_Icc_self hx),
      massDensity, massCost, massLossRate, mul_div_assoc] at hd ⊢
    linear_combination hd
  rw [heqD, heqM] at hsplit
  change (∫ᵛ x, c x ∂[derivativePairing; ν]) = _ at hchain
  linarith

end
end krylov.ContinuumBV
