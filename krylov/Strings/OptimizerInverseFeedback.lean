import krylov.Strings.OptimizerClosedLoop
import krylov.Strings.AtomicState
import krylov.Strings.FeedbackMassInvariant

/-!
Article: main_krylov, thm:value, equality implies the actual feedback ODE.
Use: recover continuity and differentiability of the actual measure-defined
state from vanishing singular mass and the actual almost-everywhere feedback
density. The origin atom is retained; derivatives there are from the right.
Source: the actual left/right state limits, RN decomposition and FTC.
-/

namespace krylov.Strings
noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal

namespace Mass

/-- Positive atomlessness makes the mass primitive continuous; its windows exclude the unit origin atom. -/
theorem cumulativeIntegral_continuous_of_no_atoms (M : Mass) {f : ℝ → ℝ}
    (hc : Continuous f) (ha : ∀ x > 0, M.measure {x} = 0) :
    Continuous (fun x ↦ ∫ t in Ioc 0 x, f t ∂M.measure) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  have heq : (∫ t in Ioo 0 x, f t ∂M.measure) = ∫ t in Ioc 0 x, f t ∂M.measure := by
    by_cases hx : 0 < x
    · have hh := M.cumulativeIntegral_atom hc hx
      have hz : M.measure.real {x} = 0 := by simp [Measure.real, ha x hx]
      simpa only [hz, zero_mul, add_zero] using hh.symm
    · have hx' : x ≤ 0 := not_lt.mp hx
      simp [Ioo_eq_empty_of_le hx', Ioc_eq_empty_of_le hx']
  apply continuousAt_iff_continuous_left'_right'.2
  exact ⟨by change Tendsto _ (𝓝[<] x) _
            simpa only [heq] using M.cumulativeIntegral_tendsto_left hc x,
    (M.cumulativeIntegral_right_continuous hc x).mono Ioi_subset_Ici_self⟩

/-- The actual integral slope is continuous in the absence of positive atoms. -/
theorem slope_continuous_of_no_atoms (M : Mass) {φ : ℝ → ℝ} (hc : Continuous φ)
    (ha : ∀ x > 0, M.measure {x} = 0) : Continuous (integralSlope M.measure φ) :=
  continuous_const.add (M.cumulativeIntegral_continuous_of_no_atoms hc ha)

/-- The actual integral energy is continuous in the absence of positive atoms. -/
theorem energy_continuous_of_no_atoms (M : Mass) {φ : ℝ → ℝ} (hc : Continuous φ)
    (ha : ∀ x > 0, M.measure {x} = 0) : Continuous (integralEnergy M.measure φ) :=
  continuous_const.add (M.cumulativeIntegral_continuous_of_no_atoms (hc.pow 2) ha)

/-- Vanishing singular mass and the actual RN density identify the actual
measure on a compact positive window. -/
theorem restrict_eq_density_of_singular_zero (M : Mass) {v : ℝ → ℝ} (L : ℝ≥0)
    (hs : (M.measure.singularPart volume) (Ioc 0 (L : ℝ)) = 0)
    (hv : M.typeDensity =ᵐ[volume.restrict (Ioc 0 (L : ℝ))] v) :
    M.measure.restrict (Ioc 0 (L : ℝ)) =
      (krylov.ContinuumControl.densityMass v).restrict (Ioc 0 (L : ℝ)) := by
  have hdec := congrArg (fun μ : Measure ℝ ↦ μ.restrict (Ioc 0 (L : ℝ))) M.type_mass_decomposition
  rw [Measure.restrict_add, Measure.restrict_eq_zero.mpr hs, add_zero] at hdec
  rw [← hdec, krylov.ContinuumControl.densityMass, restrict_withDensity measurableSet_Ioc,
    restrict_withDensity measurableSet_Ioc]
  exact withDensity_congr_ae (hv.fun_comp (fun z : ℝ ↦ ENNReal.ofReal (z ^ 2)))

end Mass

/-- The physical position paired with its actual mass-integral slope and energy. -/
def actualFeedbackState (M : Mass) (φ : ℝ → ℝ) (x : ℝ) : FeedbackState :=
  (φ x, integralSlope M.measure φ x, integralEnergy M.measure φ x)

/-- The named-graph density law evaluated on the actual mass-defined state. -/
def actualFeedbackDensity (M : Mass) (φ σ : ℝ → ℝ) : ℝ → ℝ :=
  feedbackCurveDensity σ (actualFeedbackState M φ)

/-- Extend actual feedback from the source half-line by its initial value. -/
def clampedFeedbackDensity (M : Mass) (φ σ : ℝ → ℝ) (x : ℝ) : ℝ :=
  actualFeedbackDensity M φ σ (max x 0)

/-- Positive atomlessness gives a continuous actual feedback density on the source domain. -/
theorem actualFeedbackDensity_continuousOn (M : Mass) {φ σ : ℝ → ℝ}
    (hc : Continuous φ) (hm : Monotone φ) (h₀ : φ 0 = 1)
    (ha : ∀ x > 0, M.measure {x} = 0)
    (hσ : ∀ r ≥ 1, ContinuousAt σ r) (hσpos : ∀ r ≥ 1, 0 < σ r) :
    ContinuousOn (actualFeedbackDensity M φ σ) (Ici 0) := by
  have hp := M.slope_continuous_of_no_atoms hc ha
  have hK := M.energy_continuous_of_no_atoms hc ha
  have hKn : ∀ x, integralEnergy M.measure φ x ≠ 0 :=
    fun x ↦ ne_of_gt (zero_lt_one.trans_le (integralEnergy_one_le _ _ x))
  have hr : Continuous (fun x ↦ stateRatio (φ x) (integralSlope M.measure φ x)
      (integralEnergy M.measure φ x)) := by
    exact (hc.mul hp).div hK hKn
  intro x hx
  have hratio := mass_state_ratio_ge_one M hx h₀ hc.continuousOn (hm.monotoneOn _)
  have hsx : ContinuousAt (fun y ↦ σ (stateRatio (φ y) (integralSlope M.measure φ y)
      (integralEnergy M.measure φ y))) x :=
    (hσ _ hratio).tendsto.comp hr.continuousAt.tendsto
  have hφ : 0 < φ x := by
    have hh := hm hx
    rw [h₀] at hh
    linarith
  change ContinuousWithinAt
    (fun y ↦ integralSlope M.measure φ y /
      (φ y * Real.sqrt (σ (stateRatio (φ y) (integralSlope M.measure φ y)
        (integralEnergy M.measure φ y))))) (Ici 0) x
  exact (hp.continuousAt.div (hc.continuousAt.mul hsx.sqrt)
    (mul_ne_zero hφ.ne' (Real.sqrt_pos.mpr (hσpos _ hratio)).ne')).continuousWithinAt

/-- Clamping the source feedback density gives a continuous real-line representative. -/
theorem clampedFeedbackDensity_continuous (M : Mass) {φ σ : ℝ → ℝ}
    (hc : Continuous φ) (hm : Monotone φ) (h₀ : φ 0 = 1)
    (ha : ∀ x > 0, M.measure {x} = 0)
    (hσ : ∀ r ≥ 1, ContinuousAt σ r) (hσpos : ∀ r ≥ 1, 0 < σ r) :
    Continuous (clampedFeedbackDensity M φ σ) :=
  (actualFeedbackDensity_continuousOn M hc hm h₀ ha hσ hσpos).comp_continuous
    (continuous_id.max continuous_const) (fun x ↦ le_max_right x 0)

namespace Mass

/-- Local measure agreement identifies the actual slope with its continuous-density primitive. -/
theorem slope_eq_density_primitive (M : Mass) {φ v : ℝ → ℝ} (hv : Continuous v)
    (hμ : ∀ L : ℝ≥0, M.measure.restrict (Ioc 0 (L : ℝ)) =
      (krylov.ContinuumControl.densityMass v).restrict (Ioc 0 (L : ℝ)))
    {x : ℝ} (hx : 0 ≤ x) :
    integralSlope M.measure φ x = 1 + OptimizerQuadratures.primitive (fun t ↦ φ t * v t ^ 2) x := by
  have h := hμ (⟨x, hx⟩ : ℝ≥0)
  change M.measure.restrict (Ioc 0 x) =
    (krylov.ContinuumControl.densityMass v).restrict (Ioc 0 x) at h
  dsimp [integralSlope, OptimizerQuadratures.primitive]
  rw [h, krylov.ContinuumControl.integral_densityMass v φ hv.measurable hx]

/-- Local measure agreement identifies the actual energy with its continuous-density primitive. -/
theorem energy_eq_density_primitive (M : Mass) {φ v : ℝ → ℝ} (hv : Continuous v)
    (hμ : ∀ L : ℝ≥0, M.measure.restrict (Ioc 0 (L : ℝ)) =
      (krylov.ContinuumControl.densityMass v).restrict (Ioc 0 (L : ℝ)))
    {x : ℝ} (hx : 0 ≤ x) :
    integralEnergy M.measure φ x = 1 + OptimizerQuadratures.primitive (fun t ↦ φ t ^ 2 * v t ^ 2) x := by
  have h := hμ (⟨x, hx⟩ : ℝ≥0)
  change M.measure.restrict (Ioc 0 x) =
    (krylov.ContinuumControl.densityMass v).restrict (Ioc 0 x) at h
  dsimp [integralEnergy, OptimizerQuadratures.primitive]
  rw [h, krylov.ContinuumControl.integral_densityMass v (fun t ↦ φ t ^ 2) hv.measurable hx]

/-- FTC for the actual mass-defined state, including the correct right
derivative at zero. -/
theorem actualState_hasDerivWithinAt_of_density (M : Mass) {φ v : ℝ → ℝ}
    (hc : Continuous φ) (hv : Continuous v) (ha : ∀ x > 0, M.measure {x} = 0)
    (he : ∀ x ≥ 0, φ x = 1 + ∫ t in Ioc 0 x, integralSlope M.measure φ t)
    (hμ : ∀ L : ℝ≥0, M.measure.restrict (Ioc 0 (L : ℝ)) =
      (krylov.ContinuumControl.densityMass v).restrict (Ioc 0 (L : ℝ)))
    {x : ℝ} (hx : 0 ≤ x) :
    HasDerivWithinAt (actualFeedbackState M φ)
      (integralSlope M.measure φ x, φ x * v x ^ 2, φ x ^ 2 * v x ^ 2) (Ici 0) x := by
  have hp := M.slope_continuous_of_no_atoms hc ha
  have hφ := ((OptimizerQuadratures.primitive_derivative hp x).const_add 1).hasDerivWithinAt (s := Ici 0)
  have hdp := ((OptimizerQuadratures.primitive_derivative (hc.mul (hv.pow 2)) x).const_add 1).hasDerivWithinAt (s := Ici 0)
  have hdK := ((OptimizerQuadratures.primitive_derivative ((hc.pow 2).mul (hv.pow 2)) x).const_add 1).hasDerivWithinAt (s := Ici 0)
  have hφ' : HasDerivWithinAt φ (integralSlope M.measure φ x) (Ici 0) x := by
    apply hφ.congr
    · intro y hy
      simpa only [OptimizerQuadratures.primitive, intervalIntegral.integral_of_le hy] using he y hy
    · simpa only [OptimizerQuadratures.primitive, intervalIntegral.integral_of_le hx] using he x hx
  have hp' : HasDerivWithinAt (integralSlope M.measure φ) (φ x * v x ^ 2) (Ici 0) x :=
    hdp.congr (fun y hy ↦ M.slope_eq_density_primitive hv hμ hy) (M.slope_eq_density_primitive hv hμ hx)
  have hK' : HasDerivWithinAt (integralEnergy M.measure φ) (φ x ^ 2 * v x ^ 2) (Ici 0) x :=
    hdK.congr (fun y hy ↦ M.energy_eq_density_primitive hv hμ hy) (M.energy_eq_density_primitive hv hμ hx)
  exact hφ'.prodMk (hp'.prodMk hK')

end Mass

/-- Equality's actual measure and density consequences force the actual
closed-loop ODE. The statement uses right derivatives at the origin and
ordinary derivatives at every strictly positive position. -/
theorem actualFeedbackState_hasDerivWithinAt (M : Mass) {φ σ : ℝ → ℝ}
    (hc : Continuous φ) (hm : Monotone φ) (h₀ : φ 0 = 1)
    (he : ∀ x ≥ 0, φ x = 1 + ∫ t in Ioc 0 x, integralSlope M.measure φ t)
    (ha : ∀ x > 0, M.measure {x} = 0)
    (hσ : ∀ r ≥ 1, ContinuousAt σ r) (hσpos : ∀ r ≥ 1, 0 < σ r)
    (hSing : ∀ L : ℝ≥0, (M.measure.singularPart volume) (Ioc 0 (L : ℝ)) = 0)
    (hfb : ∀ L : ℝ≥0, M.typeDensity =ᵐ[volume.restrict (Ioc 0 (L : ℝ))]
      actualFeedbackDensity M φ σ) {x : ℝ} (hx : 0 ≤ x) :
    HasDerivWithinAt (actualFeedbackState M φ)
      (feedbackField σ (actualFeedbackState M φ x)) (Ici 0) x := by
  let v := clampedFeedbackDensity M φ σ
  have hv : Continuous v := clampedFeedbackDensity_continuous M hc hm h₀ ha hσ hσpos
  have hvfb (L : ℝ≥0) : M.typeDensity =ᵐ[volume.restrict (Ioc 0 (L : ℝ))] v := by
    filter_upwards [hfb L, ae_restrict_mem measurableSet_Ioc] with y hy hym
    simpa only [v, clampedFeedbackDensity, max_eq_left hym.1.le] using hy
  have hμ (L : ℝ≥0) : M.measure.restrict (Ioc 0 (L : ℝ)) =
      (krylov.ContinuumControl.densityMass v).restrict (Ioc 0 (L : ℝ)) :=
    M.restrict_eq_density_of_singular_zero L (hSing L) (hvfb L)
  have hd := M.actualState_hasDerivWithinAt_of_density hc hv ha he hμ hx
  have hratio := mass_state_ratio_ge_one M hx h₀ hc.continuousOn (hm.monotoneOn _)
  have hφ : 0 < φ x := by
    have hh := hm hx
    rw [h₀] at hh
    linarith
  have hσp := hσpos _ hratio
  have hvx : v x = feedbackDensity (φ x) (integralSlope M.measure φ x)
      (Real.sqrt (σ (stateRatio (φ x) (integralSlope M.measure φ x) (integralEnergy M.measure φ x)))) := by
    dsimp [v, clampedFeedbackDensity]
    rw [max_eq_left hx]
    rfl
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

/-- The recovered actual state satisfies the ordinary feedback ODE at positive positions. -/
theorem actualFeedbackState_hasDerivAt (M : Mass) {φ σ : ℝ → ℝ}
    (hc : Continuous φ) (hm : Monotone φ) (h₀ : φ 0 = 1)
    (he : ∀ x ≥ 0, φ x = 1 + ∫ t in Ioc 0 x, integralSlope M.measure φ t)
    (ha : ∀ x > 0, M.measure {x} = 0)
    (hσ : ∀ r ≥ 1, ContinuousAt σ r) (hσpos : ∀ r ≥ 1, 0 < σ r)
    (hSing : ∀ L : ℝ≥0, (M.measure.singularPart volume) (Ioc 0 (L : ℝ)) = 0)
    (hfb : ∀ L : ℝ≥0, M.typeDensity =ᵐ[volume.restrict (Ioc 0 (L : ℝ))]
      actualFeedbackDensity M φ σ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (actualFeedbackState M φ) (feedbackField σ (actualFeedbackState M φ x)) x :=
  (actualFeedbackState_hasDerivWithinAt M hc hm h₀ he ha hσ hσpos hSing hfb hx.le).hasDerivAt
    (Ici_mem_nhds hx)

end
end krylov.Strings
