import krylov.ContinuumBV.ActualPhysical
import krylov.Strings.Reward

/-!
Article: main_krylov, apC:eq:fundamental, continuous and singular continuous mass.
Use: split the actual physical identity by the actual Lebesgue decomposition,
and complete the square with the actual square-root RN density. The singular
measure is retained, including its possible singular continuous component.
Source: mathlib Lebesgue decomposition and the proved physical BV identity.
-/

namespace krylov.ContinuumBV
noncomputable section
open Set Filter MeasureTheory
open krylov.Strings krylov.ContinuumControl
open scoped Topology NNReal

/-- The nonnegative square term in the fundamental identity, evaluated at the
actual state and the actual square-root Radon–Nikodym density. -/
def actualSquareCost (M : Mass) (γ : ℝ) (σ φ : ℝ → ℝ) (x : ℝ) : ℝ :=
  (integralEnergy M.measure φ x) ^ (-γ) *
    (Real.sqrt (integralSlope M.measure φ x /
        (φ x * Real.sqrt (σ (φ x * integralSlope M.measure φ x / integralEnergy M.measure φ x)))) -
      M.typeDensity x * Real.sqrt (φ x *
        Real.sqrt (σ (φ x * integralSlope M.measure φ x / integralEnergy M.measure φ x)) /
          integralSlope M.measure φ x)) ^ 2

/-- Any actually integrable mass cost splits into its absolutely continuous
and singular integrals. This lemma does not exclude atoms or assume a density. -/
theorem actual_mass_integral_split (M : Mass) {g : ℝ → ℝ} {a b : ℝ}
    (hi : IntegrableOn g (Ioc a b) M.measure) :
    IntegrableOn (fun x => M.typeDensity x ^ 2 * g x) (Ioc a b) ∧
      IntegrableOn g (Ioc a b) (M.measure.singularPart volume) ∧
      (∫ x in Ioc a b, g x ∂M.measure) =
        (∫ x in Ioc a b, M.typeDensity x ^ 2 * g x) +
          (∫ x in Ioc a b, g x ∂M.measure.singularPart volume) := by
  have hf : Measurable (fun x => ENNReal.ofReal (M.typeDensity x ^ 2)) :=
    (M.measurable_typeDensity.pow_const 2).ennreal_ofReal
  have ht : ∀ᵐ x ∂volume.restrict (Ioc a b),
      ENNReal.ofReal (M.typeDensity x ^ 2) < ⊤ := by simp
  have hsplit : Integrable g
      ((volume.withDensity (fun x => ENNReal.ofReal (M.typeDensity x ^ 2))).restrict (Ioc a b) +
        (M.measure.singularPart volume).restrict (Ioc a b)) := by
    rw [← Measure.restrict_add, M.type_mass_decomposition]
    exact hi
  have ha := hsplit.left_of_add_measure
  have hs := hsplit.right_of_add_measure
  have ha' : IntegrableOn (fun x => M.typeDensity x ^ 2 * g x) (Ioc a b) := by
    rw [restrict_withDensity measurableSet_Ioc] at ha
    simpa only [ENNReal.toReal_ofReal (sq_nonneg _), smul_eq_mul, IntegrableOn] using
      (integrable_withDensity_iff_integrable_smul' hf ht).1 ha
  refine ⟨ha', hs, ?_⟩
  have he := integral_add_measure ha hs
  rw [← Measure.restrict_add, M.type_mass_decomposition] at he
  rw [setIntegral_withDensity_eq_setIntegral_toReal_smul hf ht _ measurableSet_Ioc] at he
  simpa only [ENNReal.toReal_ofReal (sq_nonneg _), smul_eq_mul] using he

/-- On an atom-free physical window the actual drift and mass costs are
continuous. This proves all cost integrability used in the decomposition. -/
theorem actual_costs_continuousOn (M : Mass) {φ : ℝ → ℝ}
    (hc : Continuous φ) (hm : Monotone φ) (h₀ : φ 0 = 1) (L : ℝ≥0)
    (hAtom : ∀ x ∈ Ioc 0 (L : ℝ), M.measure {x} = 0)
    {γ : ℝ} {σ : ℝ → ℝ}
    (hσ : ∀ r, 1 ≤ r → ContDiffAt ℝ 1 σ r)
    (hσpos : ∀ r, 1 ≤ r → 0 < σ r) :
    ContinuousOn (driftCost M γ σ φ) (Icc 0 (L : ℝ)) ∧
      ContinuousOn (massCost M γ σ φ) (Icc 0 (L : ℝ)) := by
  have hcost : ∀ x ∈ Icc 0 (L : ℝ),
      ContinuousAt (driftCost M γ σ φ) x ∧ ContinuousAt (massCost M γ σ φ) x := by
    intro x hx
    have hp := actual_slope_continuousAt M hc hm h₀ hx.1 (fun hp => hAtom x ⟨hp, hx.2⟩)
    have hK := actual_energy_continuousAt M hc hx.1 (fun hp => hAtom x ⟨hp, hx.2⟩)
    have hdom := compactStateDomain_positive_ratio M φ L (clippedState_mem M hc hm h₀ L x)
    simp only [clippedState, clipTime_of_mem L hx] at hdom
    obtain ⟨hφ, hpp, hKK, hr⟩ := hdom
    have ht := ((hσ _ hr).continuousAt.comp (f := fun y =>
      φ y * integralSlope M.measure φ y / integralEnergy M.measure φ y)
      ((hc.continuousAt.mul hp).div hK hKK.ne')).sqrt
    have hpow := hK.rpow_const (Or.inl hKK.ne') (p := -γ)
    exact ⟨((hpow.mul hp).div (hc.continuousAt.mul ht)
      (mul_pos hφ (Real.sqrt_pos.2 (hσpos _ hr))).ne'),
      (((hpow.mul hc.continuousAt).mul ht).div hp hpp.ne')⟩
  exact ⟨fun x hx => (hcost x hx).1.continuousWithinAt,
    fun x hx => (hcost x hx).2.continuousWithinAt⟩

/-- Pointwise square completion for the actual string, rather than an
independent control profile. -/
theorem actualSquareCost_eq (M : Mass) {φ : ℝ → ℝ}
    (hm : Monotone φ) (h₀ : φ 0 = 1)
    {γ x : ℝ} {σ : ℝ → ℝ} (hx : 0 ≤ x)
    (hσpos : 0 < σ (φ x * integralSlope M.measure φ x / integralEnergy M.measure φ x)) :
    actualSquareCost M γ σ φ x = driftCost M γ σ φ x +
      M.typeDensity x ^ 2 * massCost M γ σ φ x - 2 * M.rewardDensity γ φ x := by
  have hφ : 0 < φ x := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (by simpa [h₀] using hm hx)
  have hp : 0 < integralSlope M.measure φ x := lt_of_lt_of_le (by norm_num) (M.slope_one_le hm h₀ x)
  have he := drift_mass_square hφ hp (Real.sqrt_pos.2 hσpos) (M.typeDensity x)
  dsimp only [actualSquareCost, driftCost, massCost, massLossRate, Mass.rewardDensity]
  linear_combination -2 * (integralEnergy M.measure φ x) ^ (-γ) * he

/-- The complete physical fundamental identity on an atom-free window.
The mass may have arbitrary singular continuous part; its positive loss is
the final integral, and the reward uses the actual RN type density. -/
theorem actual_continuous_fundamental_identity (M : Mass) {φ : ℝ → ℝ}
    (hc : Continuous φ) (hm : Monotone φ) (h₀ : φ 0 = 1) (L : ℝ≥0)
    (he : ∀ x ∈ Icc 0 (L : ℝ), φ x = 1 + ∫ t in Ioc 0 x, integralSlope M.measure φ t)
    (hAtom : ∀ x ∈ Ioc 0 (L : ℝ), M.measure {x} = 0)
    {γ : ℝ} {σ : ℝ → ℝ} (hγ : 0 < γ)
    (hσ : ∀ r, 1 ≤ r → ContDiffAt ℝ 1 σ r)
    (hgraph : ∀ r, 1 ≤ r → FeedbackGraphAt γ σ r) :
    statePotential γ σ (clippedState M φ L 0) - statePotential γ σ (clippedState M φ L L) =
      (∫ x in Ioc 0 (L : ℝ), M.rewardDensity γ φ x) +
        1 / 2 * (∫ x in Ioc 0 (L : ℝ), actualSquareCost M γ σ φ x) +
        1 / 2 * (∫ x in Ioc 0 (L : ℝ), massCost M γ σ φ x ∂M.measure.singularPart volume) := by
  have hcost := actual_costs_continuousOn M hc hm h₀ L hAtom (γ := γ) hσ
    (fun r hr => (hgraph r hr).positive)
  have hd : IntegrableOn (driftCost M γ σ φ) (Ioc 0 (L : ℝ)) :=
    (hcost.1.integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self
  let : IsLocallyFiniteMeasure M.measure := by dsimp [Mass.measure]; infer_instance
  have hmi : IntegrableOn (massCost M γ σ φ) (Ioc 0 (L : ℝ)) M.measure :=
    (hcost.2.integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self
  obtain ⟨ha, hs, hsplit⟩ := actual_mass_integral_split M hmi
  have hr := M.rewardDensity_integrableOn hγ.le hc 0 L
  have hsq : EqOn (actualSquareCost M γ σ φ) (fun x => driftCost M γ σ φ x +
      M.typeDensity x ^ 2 * massCost M γ σ φ x - 2 * M.rewardDensity γ φ x) (Ioc 0 (L : ℝ)) := by
    intro x hx
    have hp := compactStateDomain_positive_ratio M φ L (clippedState_mem M hc hm h₀ L x)
    simp only [clippedState, clipTime_of_mem L (Ioc_subset_Icc_self hx)] at hp
    exact actualSquareCost_eq M hm h₀ hx.1.le (hgraph _ hp.2.2.2).positive
  have hi : IntegrableOn (actualSquareCost M γ σ φ) (Ioc 0 (L : ℝ)) :=
    (integrableOn_congr_fun hsq measurableSet_Ioc).2 ((hd.add ha).sub (hr.const_mul 2))
  have hsquare : (∫ x in Ioc 0 (L : ℝ), actualSquareCost M γ σ φ x) =
      (∫ x in Ioc 0 (L : ℝ), driftCost M γ σ φ x) +
        (∫ x in Ioc 0 (L : ℝ), M.typeDensity x ^ 2 * massCost M γ σ φ x) -
          2 * (∫ x in Ioc 0 (L : ℝ), M.rewardDensity γ φ x) := by
    rw [setIntegral_congr_fun measurableSet_Ioc hsq]
    simpa only [Pi.add_apply, integral_add hd ha, integral_const_mul] using
      integral_sub (hd.add ha) (hr.const_mul 2)
  have hid := actual_continuous_physical_identity M hc hm h₀ L he hAtom hγ.ne' hσ hgraph
  linarith

end
end krylov.ContinuumBV
