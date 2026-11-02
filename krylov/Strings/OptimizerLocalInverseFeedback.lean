import krylov.Strings.OptimizerInverseFeedback

/-!
Article: main_krylov, thm:value, finite-length equality localization.
Use: recover the actual right feedback ODE strictly before a finite window
endpoint from equality consequences available only on that window. No
feedback law is imposed outside the window.
Source: actual atom-free state limits, local RN decomposition and local FTC.
-/

namespace krylov.Strings
noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal

namespace Mass

/-- The mass primitive is continuous at a point with no positive atom there. -/
theorem cumulativeIntegral_continuousAt_of_atom_zero (M : Mass) {f : ℝ → ℝ}
    (hc : Continuous f) (x : ℝ) (ha : 0 < x → M.measure {x} = 0) :
    ContinuousAt (fun y ↦ ∫ t in Ioc 0 y, f t ∂M.measure) x := by
  have heq : (∫ t in Ioo 0 x, f t ∂M.measure) = ∫ t in Ioc 0 x, f t ∂M.measure := by
    by_cases hx : 0 < x
    · have hh := M.cumulativeIntegral_atom hc hx
      have hz : M.measure.real {x} = 0 := by simp [Measure.real, ha hx]
      simpa only [hz, zero_mul, add_zero] using hh.symm
    · have hx' : x ≤ 0 := not_lt.mp hx
      simp [Ioo_eq_empty_of_le hx', Ioc_eq_empty_of_le hx']
  apply continuousAt_iff_continuous_left'_right'.2
  exact ⟨by change Tendsto _ (𝓝[<] x) _
            simpa only [heq] using M.cumulativeIntegral_tendsto_left hc x,
    (M.cumulativeIntegral_right_continuous hc x).mono Ioi_subset_Ici_self⟩

/-- Positive atomlessness on a compact window gives continuity of the actual state there. -/
theorem actualFeedbackState_continuousOn_window (M : Mass) {φ : ℝ → ℝ} (L : ℝ≥0)
    (hc : Continuous φ) (ha : ∀ x ∈ Ioc 0 (L : ℝ), M.measure {x} = 0) :
    ContinuousOn (actualFeedbackState M φ) (Icc 0 (L : ℝ)) := by
  intro x hx
  have hz : 0 < x → M.measure {x} = 0 := fun hxp ↦ ha x ⟨hxp, hx.2⟩
  exact (hc.continuousAt.prodMk ((continuousAt_const.add
    (M.cumulativeIntegral_continuousAt_of_atom_zero hc x hz)).prodMk
    (continuousAt_const.add (M.cumulativeIntegral_continuousAt_of_atom_zero (hc.pow 2) x hz)))).continuousWithinAt

/-- The actual named-graph density is continuous on an atomless source window. -/
theorem actualFeedbackDensity_continuousOn_window (M : Mass) {φ σ : ℝ → ℝ} (L : ℝ≥0)
    (hc : Continuous φ) (hm : Monotone φ) (h₀ : φ 0 = 1)
    (ha : ∀ x ∈ Ioc 0 (L : ℝ), M.measure {x} = 0)
    (hσ : ∀ r ≥ 1, ContinuousAt σ r) (hσpos : ∀ r ≥ 1, 0 < σ r) :
    ContinuousOn (actualFeedbackDensity M φ σ) (Icc 0 (L : ℝ)) := by
  intro x hx
  have hzero : 0 < x → M.measure {x} = 0 := fun hxp ↦ ha x ⟨hxp, hx.2⟩
  have hp : ContinuousAt (integralSlope M.measure φ) x :=
    continuousAt_const.add (M.cumulativeIntegral_continuousAt_of_atom_zero hc x hzero)
  have hK : ContinuousAt (integralEnergy M.measure φ) x :=
    continuousAt_const.add (M.cumulativeIntegral_continuousAt_of_atom_zero (hc.pow 2) x hzero)
  have hr : ContinuousAt (fun y ↦ stateRatio (φ y) (integralSlope M.measure φ y)
      (integralEnergy M.measure φ y)) x :=
    (hc.continuousAt.mul hp).div hK (ne_of_gt (zero_lt_one.trans_le (integralEnergy_one_le _ _ x)))
  have hratio := mass_state_ratio_ge_one M hx.1 h₀ hc.continuousOn (hm.monotoneOn _)
  have hsx : ContinuousAt (fun y ↦ σ (stateRatio (φ y) (integralSlope M.measure φ y)
      (integralEnergy M.measure φ y))) x := (hσ _ hratio).tendsto.comp hr.tendsto
  have hφ : 0 < φ x := by
    have hh := hm hx.1
    rw [h₀] at hh
    linarith
  exact (hp.div (hc.continuousAt.mul hsx.sqrt)
    (mul_ne_zero hφ.ne' (Real.sqrt_pos.mpr (hσpos _ hratio)).ne')).continuousWithinAt

end Mass

/-- The actual window feedback density extended by clamping to the two endpoints. -/
def windowFeedbackDensity (M : Mass) (φ σ : ℝ → ℝ) (L : ℝ≥0) (x : ℝ) : ℝ :=
  actualFeedbackDensity M φ σ (max 0 (min x (L : ℝ)))

/-- The clamped representative equals actual feedback inside its defining window. -/
theorem windowFeedbackDensity_eq (M : Mass) (φ σ : ℝ → ℝ) (L : ℝ≥0) {x : ℝ}
    (hx : x ∈ Icc 0 (L : ℝ)) : windowFeedbackDensity M φ σ L x = actualFeedbackDensity M φ σ x := by
  simp only [windowFeedbackDensity, min_eq_left hx.2, max_eq_right hx.1]

/-- The clamped window feedback representative is continuous on the real line. -/
theorem windowFeedbackDensity_continuous (M : Mass) {φ σ : ℝ → ℝ} (L : ℝ≥0)
    (hc : Continuous φ) (hm : Monotone φ) (h₀ : φ 0 = 1)
    (ha : ∀ x ∈ Ioc 0 (L : ℝ), M.measure {x} = 0)
    (hσ : ∀ r ≥ 1, ContinuousAt σ r) (hσpos : ∀ r ≥ 1, 0 < σ r) :
    Continuous (windowFeedbackDensity M φ σ L) := by
  apply (M.actualFeedbackDensity_continuousOn_window L hc hm h₀ ha hσ hσpos).comp_continuous
    (continuous_const.max (continuous_id.min continuous_const))
  intro x
  exact ⟨le_max_left _ _, max_le L.property (min_le_right _ _)⟩

namespace Mass

/-- Local density agreement recovers the actual state ODE from the right before the window endpoint. -/
theorem actualState_hasDerivWithinAt_of_local_density (M : Mass) {φ v : ℝ → ℝ} (L : ℝ≥0)
    (hc : Continuous φ) (hv : Continuous v)
    (ha : ∀ x ∈ Ioc 0 (L : ℝ), M.measure {x} = 0)
    (he : ∀ x ∈ Icc 0 (L : ℝ), φ x = 1 + ∫ t in Ioc 0 x, integralSlope M.measure φ t)
    (hμ : M.measure.restrict (Ioc 0 (L : ℝ)) =
      (krylov.ContinuumControl.densityMass v).restrict (Ioc 0 (L : ℝ)))
    {x : ℝ} (hx : x ∈ Ico 0 (L : ℝ)) :
    HasDerivWithinAt (actualFeedbackState M φ)
      (integralSlope M.measure φ x, φ x * v x ^ 2, φ x ^ 2 * v x ^ 2) (Ici 0) x := by
  have hpAt (y : ℝ) (hy : y ∈ Icc 0 (L : ℝ)) : ContinuousAt (integralSlope M.measure φ) y :=
    continuousAt_const.add (M.cumulativeIntegral_continuousAt_of_atom_zero hc y (fun hyp ↦ ha y ⟨hyp, hy.2⟩))
  have hpI : IntervalIntegrable (integralSlope M.measure φ) volume 0 x :=
    (show ContinuousOn (integralSlope M.measure φ) (Icc 0 x) from
      fun y hy ↦ (hpAt y ⟨hy.1, hy.2.trans hx.2.le⟩).continuousWithinAt).intervalIntegrable_of_Icc hx.1
  have hpOpen (y : ℝ) (hy : y ∈ Iio (L : ℝ)) : ContinuousAt (integralSlope M.measure φ) y :=
    continuousAt_const.add (M.cumulativeIntegral_continuousAt_of_atom_zero hc y
      (fun hyp ↦ ha y ⟨hyp, hy.le⟩))
  have hdprefix := (intervalIntegral.integral_hasDerivAt_right hpI
    (ContinuousAt.stronglyMeasurableAtFilter isOpen_Iio hpOpen x hx.2)
    (hpAt x ⟨hx.1, hx.2.le⟩)).const_add 1
  have heqμ (y : ℝ) (hy : y ∈ Icc 0 (L : ℝ)) : M.measure.restrict (Ioc 0 y) =
      (krylov.ContinuumControl.densityMass v).restrict (Ioc 0 y) := by
    have hsub : Ioc (0 : ℝ) y ⊆ Ioc 0 (L : ℝ) := fun _ ht ↦ ⟨ht.1, ht.2.trans hy.2⟩
    rw [← Measure.restrict_restrict_of_subset hsub, hμ, Measure.restrict_restrict_of_subset hsub]
  have hpEq (y : ℝ) (hy : y ∈ Icc 0 (L : ℝ)) : integralSlope M.measure φ y =
      1 + OptimizerQuadratures.primitive (fun t ↦ φ t * v t ^ 2) y := by
    dsimp [integralSlope, OptimizerQuadratures.primitive]
    rw [heqμ y hy, krylov.ContinuumControl.integral_densityMass v φ hv.measurable hy.1]
  have hKEq (y : ℝ) (hy : y ∈ Icc 0 (L : ℝ)) : integralEnergy M.measure φ y =
      1 + OptimizerQuadratures.primitive (fun t ↦ φ t ^ 2 * v t ^ 2) y := by
    dsimp [integralEnergy, OptimizerQuadratures.primitive]
    rw [heqμ y hy, krylov.ContinuumControl.integral_densityMass v (fun t ↦ φ t ^ 2) hv.measurable hy.1]
  have hnear : ∀ᶠ y in 𝓝[Ici 0] x, y ∈ Icc 0 (L : ℝ) := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hx.2).filter_mono nhdsWithin_le_nhds] with y hy₀ hyL
    exact ⟨hy₀, hyL.le⟩
  have hφ : HasDerivWithinAt φ (integralSlope M.measure φ x) (Ici 0) x := by
    apply hdprefix.hasDerivWithinAt.congr_of_eventuallyEq
    · filter_upwards [hnear] with y hy
      simpa only [intervalIntegral.integral_of_le hy.1] using he y hy
    · simpa only [intervalIntegral.integral_of_le hx.1] using he x ⟨hx.1, hx.2.le⟩
  have hp : HasDerivWithinAt (integralSlope M.measure φ) (φ x * v x ^ 2) (Ici 0) x := by
    apply ((OptimizerQuadratures.primitive_derivative (hc.mul (hv.pow 2)) x).const_add 1).hasDerivWithinAt.congr_of_eventuallyEq
    · exact hnear.mono (fun y hy ↦ hpEq y hy)
    · exact hpEq x ⟨hx.1, hx.2.le⟩
  have hK : HasDerivWithinAt (integralEnergy M.measure φ) (φ x ^ 2 * v x ^ 2) (Ici 0) x := by
    apply ((OptimizerQuadratures.primitive_derivative ((hc.pow 2).mul (hv.pow 2)) x).const_add 1).hasDerivWithinAt.congr_of_eventuallyEq
    · exact hnear.mono (fun y hy ↦ hKEq y hy)
    · exact hKEq x ⟨hx.1, hx.2.le⟩
  exact hφ.prodMk (hp.prodMk hK)

end Mass

/-- The finite-window inverse feedback bridge requires equality information
only on that window and yields the actual ODE strictly before its endpoint. -/
theorem actualFeedbackState_hasDerivWithinAt_window (M : Mass) {φ σ : ℝ → ℝ} (L : ℝ≥0)
    (hc : Continuous φ) (hm : Monotone φ) (h₀ : φ 0 = 1)
    (he : ∀ x ∈ Icc 0 (L : ℝ), φ x = 1 + ∫ t in Ioc 0 x, integralSlope M.measure φ t)
    (ha : ∀ x ∈ Ioc 0 (L : ℝ), M.measure {x} = 0)
    (hσ : ∀ r ≥ 1, ContinuousAt σ r) (hσpos : ∀ r ≥ 1, 0 < σ r)
    (hSing : (M.measure.singularPart volume) (Ioc 0 (L : ℝ)) = 0)
    (hfb : M.typeDensity =ᵐ[volume.restrict (Ioc 0 (L : ℝ))] actualFeedbackDensity M φ σ)
    {x : ℝ} (hx : x ∈ Ico 0 (L : ℝ)) :
    HasDerivWithinAt (actualFeedbackState M φ)
      (feedbackField σ (actualFeedbackState M φ x)) (Ici 0) x := by
  let v := windowFeedbackDensity M φ σ L
  have hv : Continuous v := windowFeedbackDensity_continuous M L hc hm h₀ ha hσ hσpos
  have hvfb : M.typeDensity =ᵐ[volume.restrict (Ioc 0 (L : ℝ))] v := by
    filter_upwards [hfb, ae_restrict_mem measurableSet_Ioc] with y hy hym
    exact hy.trans (windowFeedbackDensity_eq M φ σ L ⟨hym.1.le, hym.2⟩).symm
  have hμ := M.restrict_eq_density_of_singular_zero L hSing hvfb
  have hd := M.actualState_hasDerivWithinAt_of_local_density L hc hv ha he hμ hx
  have hratio := mass_state_ratio_ge_one M hx.1 h₀ hc.continuousOn (hm.monotoneOn _)
  have hφ : 0 < φ x := by
    have hh := hm hx.1
    rw [h₀] at hh
    linarith
  have hσp := hσpos _ hratio
  have hvx : v x = feedbackDensity (φ x) (integralSlope M.measure φ x)
      (Real.sqrt (σ (stateRatio (φ x) (integralSlope M.measure φ x) (integralEnergy M.measure φ x)))) :=
    windowFeedbackDensity_eq M φ σ L ⟨hx.1, hx.2.le⟩
  obtain ⟨hpRate, hKRate⟩ := feedback_physical_rates (φ x) (integralSlope M.measure φ x)
    (Real.sqrt (σ (stateRatio (φ x) (integralSlope M.measure φ x) (integralEnergy M.measure φ x))))
    (σ (stateRatio (φ x) (integralSlope M.measure φ x) (integralEnergy M.measure φ x)))
    hφ.ne' (Real.sqrt_pos.mpr hσp).ne' (Real.sq_sqrt hσp.le)
  rw [hvx] at hd
  convert hd using 1
  change (integralSlope M.measure φ x,
      integralSlope M.measure φ x ^ 2 /
        (φ x * σ (stateRatio (φ x) (integralSlope M.measure φ x) (integralEnergy M.measure φ x))),
      integralSlope M.measure φ x ^ 2 /
        σ (stateRatio (φ x) (integralSlope M.measure φ x) (integralEnergy M.measure φ x))) = _
  rw [← hpRate, ← hKRate]
  simp only [mul_comm]

end
end krylov.Strings
