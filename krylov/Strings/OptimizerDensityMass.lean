import krylov.Strings.LocalCompatibility
import krylov.ContinuumControl.DifferentialState

/-!
Article: main_krylov, thm:value, construction of the physical optimizing mass.
Use: build an actual string mass from a continuous physical density, prove
its precise density measure and identify its actual RN type clock. This is
the measure bridge needed to turn a feedback solution into a genuine string.
Source: Stieltjes window extension, FTC and uniqueness of Borel measures.
-/

namespace krylov.Strings.OptimizerDensity
noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

/-- The cumulative mass of a continuous density on a compact physical window. -/
def cumulativeWindow (v : ℝ → ℝ) (hc : Continuous v) (L : ℝ≥0) :
    StieltjesFunction (Window L) where
  toFun x := 1 + ∫ t in (0 : ℝ)..(x : ℝ), v t ^ 2
  mono' := by
    intro x y hxy
    apply add_le_add_right
    exact intervalIntegral.integral_mono_interval le_rfl x.property.1 hxy
      (Eventually.of_forall (fun t ↦ sq_nonneg (v t))) ((hc.pow 2).intervalIntegrable 0 y)
  right_continuous' := by
    intro x
    have hder := (intervalIntegral.integral_hasDerivAt_right
      (a := (0 : ℝ)) (b := (x : ℝ)) ((hc.pow 2).intervalIntegrable 0 x)
      (hc.pow 2).stronglyMeasurable.stronglyMeasurableAtFilter (hc.pow 2).continuousAt).const_add 1
    exact (hder.continuousAt.comp continuous_subtype_val.continuousAt).continuousWithinAt

/-- The cumulative mass starts with the distinguished unit atom. -/
theorem cumulativeWindow_zero (v : ℝ → ℝ) (hc : Continuous v) (L : ℝ≥0) :
    cumulativeWindow v hc L ⟨0, ⟨le_rfl, L.property⟩⟩ = 1 := by
  simp [cumulativeWindow]

/-- Actual string mass associated with the compact continuous density. -/
def mass (v : ℝ → ℝ) (hc : Continuous v) (L : ℝ≥0) : Mass :=
  LocalMass.toMass (cumulativeWindow v hc L) (cumulativeWindow_zero v hc L)

/-- The constructed cumulative mass agrees exactly with its defining integral. -/
theorem cumulative_eq (v : ℝ → ℝ) (hc : Continuous v) (L : ℝ≥0) {x : ℝ}
    (hx : x ∈ Icc 0 (L : ℝ)) :
    (mass v hc L).cumulative x = 1 + ∫ t in (0 : ℝ)..x, v t ^ 2 :=
  LocalMass.toMass_cumulative _ _ hx

/-- The actual cumulative mass has the expected right derivative at its unit
left atom. A two-sided derivative would be false because of that atom. -/
theorem cumulative_right_derivative (v : ℝ → ℝ) (hc : Continuous v) (L : ℝ≥0)
    (hL : 0 < L) :
    HasDerivWithinAt (mass v hc L).cumulative (v 0 ^ 2) (Ici 0) 0 := by
  have hd := (intervalIntegral.integral_hasDerivAt_right
    ((hc.pow 2).intervalIntegrable (μ := volume) 0 0)
    (hc.pow 2).stronglyMeasurable.stronglyMeasurableAtFilter (hc.pow 2).continuousAt).const_add 1
  apply hd.hasDerivWithinAt.congr_of_eventuallyEq_of_mem _ (by simp : (0 : ℝ) ∈ Ici 0)
  have hL' : (0 : ℝ) < (L : ℝ) := hL
  have ht : ∀ᶠ t in 𝓝[Ici (0 : ℝ)] 0, t < (L : ℝ) :=
    (eventually_lt_nhds hL').filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, ht] with t ht0 htL
  exact cumulative_eq v hc L ⟨ht0, htL.le⟩

/-- Compact increments are the actual integrals of the squared density. -/
theorem mass_Ioc (v : ℝ → ℝ) (hc : Continuous v) (L : ℝ≥0) {a b : ℝ}
    (ha : a ∈ Icc 0 (L : ℝ)) (hb : b ∈ Icc 0 (L : ℝ)) :
    (mass v hc L).measure (Ioc a b) = ENNReal.ofReal (∫ t in a..b, v t ^ 2) := by
  rw [Mass.measure_Ioc, cumulative_eq v hc L ha, cumulative_eq v hc L hb]
  have hsub := intervalIntegral.integral_interval_sub_left
    ((hc.pow 2).intervalIntegrable (μ := volume) 0 b)
    ((hc.pow 2).intervalIntegrable (μ := volume) 0 a)
  change (∫ t in (0 : ℝ)..b, v t ^ 2) - (∫ t in (0 : ℝ)..a, v t ^ 2) =
    ∫ t in a..b, v t ^ 2 at hsub
  congr 1
  linarith

/-- The constructed post-origin mass is exactly the genuine density measure
on the physical window. The initial unit atom is excluded on both sides. -/
theorem measure_restrict_eq (v : ℝ → ℝ) (hc : Continuous v) (L : ℝ≥0) :
    (mass v hc L).measure.restrict (Ioc 0 (L : ℝ)) =
      (krylov.ContinuumControl.densityMass v).restrict (Ioc 0 (L : ℝ)) := by
  have : IsFiniteMeasure ((mass v hc L).measure.restrict (Ioc 0 (L : ℝ))) := by
    constructor
    rw [Measure.restrict_apply_univ]
    exact (mass v hc L).measure_Ioc_lt_top 0 L
  apply Measure.ext_of_Ioc
  intro a b _hab
  rw [Measure.restrict_apply measurableSet_Ioc, Measure.restrict_apply measurableSet_Ioc,
    Ioc_inter_Ioc]
  by_cases hne : max a 0 < min b (L : ℝ)
  · have hlo : max a 0 ∈ Icc 0 (L : ℝ) :=
      ⟨le_max_right _ _, hne.le.trans (min_le_right _ _)⟩
    have hhi : min b (L : ℝ) ∈ Icc 0 (L : ℝ) :=
      ⟨(le_max_right _ _).trans hne.le, min_le_right _ _⟩
    rw [mass_Ioc v hc L hlo hhi, krylov.ContinuumControl.densityMass,
      withDensity_apply _ measurableSet_Ioc, intervalIntegral.integral_of_le hne.le]
    exact ofReal_integral_eq_lintegral_ofReal (hc.pow 2).integrableOn_Ioc
      (Eventually.of_forall (fun t ↦ sq_nonneg (v t)))
  · simp only [Ioc_eq_empty hne, measure_empty]

/-- The actual Radon–Nikodym type density is the absolute value of the
prescribed density almost everywhere, not an assumed choice of derivative. -/
theorem typeDensity_eq_abs_ae (v : ℝ → ℝ) (hc : Continuous v) (L : ℝ≥0) :
    (mass v hc L).typeDensity =ᵐ[volume.restrict (Ioc 0 (L : ℝ))] fun x ↦ |v x| := by
  let M := mass v hc L
  have : IsLocallyFiniteMeasure M.measure := by dsimp [M, Mass.measure]; infer_instance
  have hM := Measure.rnDeriv_restrict M.measure volume (s := Ioc (0 : ℝ) L) measurableSet_Ioc
  have hμ := measure_restrict_eq v hc L
  change M.measure.restrict (Ioc 0 (L : ℝ)) =
    (volume.withDensity (fun x ↦ ENNReal.ofReal (v x ^ 2))).restrict (Ioc 0 (L : ℝ)) at hμ
  rw [restrict_withDensity measurableSet_Ioc, ← withDensity_indicator measurableSet_Ioc] at hμ
  have hV := Measure.rnDeriv_withDensity volume
    ((ENNReal.measurable_ofReal.comp (hc.measurable.pow_const 2)).indicator
      (measurableSet_Ioc : MeasurableSet (Ioc (0 : ℝ) (L : ℝ))))
  have he := congrArg (fun μ : Measure ℝ ↦ μ.rnDeriv volume) hμ
  have h := hM.symm.trans ((EventuallyEq.of_eq he).trans hV)
  filter_upwards [ae_restrict_of_ae h, ae_restrict_mem measurableSet_Ioc] with x hx hxmem
  rw [indicator_of_mem hxmem, indicator_of_mem hxmem] at hx
  simp only [Function.comp_apply] at hx
  change Real.sqrt (M.measure.rnDeriv volume x).toReal = |v x|
  rw [hx, ENNReal.toReal_ofReal (sq_nonneg _), Real.sqrt_sq_eq_abs]

/-- For a nonnegative physical density the actual type clock is its printed
integral, on every earlier physical window. -/
theorem typeClock_eq_integral (v : ℝ → ℝ) (hc : Continuous v) (L : ℝ≥0)
    (hv : ∀ x ∈ Icc 0 (L : ℝ), 0 ≤ v x) {x : ℝ} (hx : x ∈ Icc 0 (L : ℝ)) :
    (mass v hc L).typeClock x = ∫ t in (0 : ℝ)..x, v t := by
  rw [Mass.typeClock_eq_integral _ hx.1, intervalIntegral.integral_of_le hx.1]
  apply integral_congr_ae
  have hsub : Ioc (0 : ℝ) x ⊆ Ioc 0 (L : ℝ) := fun _ ht ↦ ⟨ht.1, ht.2.trans hx.2⟩
  filter_upwards [(typeDensity_eq_abs_ae v hc L).filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl)),
    ae_restrict_mem measurableSet_Ioc] with t ht htm
  exact ht.trans (abs_of_nonneg (hv t ⟨htm.1.le, htm.2.trans hx.2⟩))

/-- A genuine smooth physical state satisfies all three printed integral
equations for the actual Stieltjes mass just constructed. In particular the
ODE is connected to the same mass whose RN derivative defines the type.
-/
theorem state_integral_equations (v : ℝ → ℝ) (hc : Continuous v) (L : ℝ≥0)
    {φ p K : ℝ → ℝ} (hφ₀ : φ 0 = 1) (hp₀ : p 0 = 1) (hK₀ : K 0 = 1)
    (hs : ∀ t ∈ Icc 0 (L : ℝ), krylov.ContinuumControl.SmoothStringAt φ p K v t)
    {x : ℝ} (hx : x ∈ Icc 0 (L : ℝ)) :
    φ x = 1 + ∫ t in Ioc 0 x, p t ∧
      p x = integralSlope (mass v hc L).measure φ x ∧
      K x = integralEnergy (mass v hc L).measure φ x := by
  have hs' : ∀ t ∈ uIcc 0 x, krylov.ContinuumControl.SmoothStringAt φ p K v t := by
    intro t ht
    rw [uIcc_of_le hx.1] at ht
    exact hs t ⟨ht.1, ht.2.trans hx.2⟩
  have he := krylov.ContinuumControl.smooth_state_measure_integral_equations hx.1 hs'
    hc.continuousOn hc.measurable
  rw [hφ₀, hp₀, hK₀, intervalIntegral.integral_of_le hx.1] at he
  have hμ : (mass v hc L).measure.restrict (Ioc 0 x) =
      (krylov.ContinuumControl.densityMass v).restrict (Ioc 0 x) := by
    have hsub : Ioc (0 : ℝ) x ⊆ Ioc 0 (L : ℝ) := fun _ ht ↦ ⟨ht.1, ht.2.trans hx.2⟩
    rw [← Measure.restrict_restrict_of_subset hsub, measure_restrict_eq,
      Measure.restrict_restrict_of_subset hsub]
  dsimp [integralSlope, integralEnergy]
  rw [hμ]
  exact he

end
end krylov.Strings.OptimizerDensity
