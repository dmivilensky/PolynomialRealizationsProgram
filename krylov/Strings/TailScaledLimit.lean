import krylov.Strings.TailCauchy
import krylov.Strings.TailScaledMeasure
import krylov.Strings.TailMeasureContinuity

/-!
Article: main_krylov, apC:prop:tauber, Stieltjes continuity at index one half.
Use: derive weak convergence of the genuine rescaled spectral measures from
the single positive-real resolvent asymptotic.  Both the limit measure and
the relative-parameter transforms are constructed, not supplied as data.
Source: the elementary half-Cauchy transform and the dense resolvent algebra.
-/

namespace krylov.Strings.Tail
noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

/-- A positive scale defined on every real input and equal to the input
eventually at positive infinity. -/
def positiveScale (t : ℝ) : PositiveParameter := ⟨max t 1, by
  change (0 : ℝ) < max t 1
  exact lt_of_lt_of_le zero_lt_one (le_max_right t 1)⟩

/-- Truncation of a scale below one does not affect its asymptotic value. -/
theorem positiveScale_eventually : ∀ᶠ t : ℝ in atTop, (positiveScale t : ℝ) = t := by
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
  change max t 1 = t
  exact max_eq_left ht

/-- The compact limit with the coefficient supplied by the real-positive
resolvent asymptotic. -/
def limitMeasure (c : ℝ≥0) : FiniteMeasure UnitInterval := c • arcsineMeasure

/-- Exact Stieltjes integrals of the coefficient-scaled limiting measure. -/
theorem kernel_integral_limitMeasure (c : ℝ≥0) (a : PositiveParameter) :
    (∫ u, kernel a u ∂limitMeasure c) = (c : ℝ) / Real.sqrt (a : ℝ) := by
  change (∫ u, kernel a u ∂((c : ℝ≥0∞) • (arcsineMeasure : Measure UnitInterval))) = _
  rw [integral_smul_measure, ENNReal.coe_toReal, smul_eq_mul, kernel_integral_arcsineMeasure]
  rfl

/-- The original real-positive Stieltjes asymptotic determines every
relative compactified transform, with the exact square-root scaling. -/
theorem tendsto_kernel_scaledMeasure (ν : FiniteMeasure ℝ)
    (hν : (ν : Measure ℝ) (Iio 0) = 0) (c : ℝ≥0)
    (hres : Tendsto (fun t : ℝ ↦ Real.sqrt t * ∫ ξ, ξ / (ξ + t) ∂ν)
      atTop (𝓝 (c : ℝ))) (a : PositiveParameter) :
    Tendsto (fun t : ℝ ↦ ∫ u, kernel a u ∂scaledMeasure ν (positiveScale t))
      atTop (𝓝 ((c : ℝ) / Real.sqrt (a : ℝ))) := by
  have ht : Tendsto (fun t : ℝ ↦ (a : ℝ) * t) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos a.property).mpr tendsto_id
  have hh := (hres.comp ht).div_const (Real.sqrt (a : ℝ))
  apply hh.congr'
  filter_upwards [positiveScale_eventually, eventually_ge_atTop (1 : ℝ)] with t he ht
  dsimp only [Function.comp_def]
  rw [kernel_integral_scaledMeasure ν hν, he, Real.sqrt_mul a.property.le]
  field_simp [(Real.sqrt_pos.mpr a.property).ne']

/-- The actual compact rescalings converge weakly to the explicit
half-Cauchy pushforward whenever the real resolvent has the half-power law. -/
theorem tendsto_scaledMeasure (ν : FiniteMeasure ℝ)
    (hν : (ν : Measure ℝ) (Iio 0) = 0) (c : ℝ≥0)
    (hres : Tendsto (fun t : ℝ ↦ Real.sqrt t * ∫ ξ, ξ / (ξ + t) ∂ν)
      atTop (𝓝 (c : ℝ))) :
    Tendsto (fun t : ℝ ↦ scaledMeasure ν (positiveScale t)) atTop (𝓝 (limitMeasure c)) := by
  have hmass : Tendsto (fun t : ℝ ↦ ((scaledMeasure ν (positiveScale t)).mass : ℝ))
      atTop (𝓝 (c : ℝ)) := by
    have hh := tendsto_kernel_scaledMeasure ν hν c hres ⟨1, by norm_num⟩
    have he (μ : FiniteMeasure UnitInterval) : (∫ u : UnitInterval, (1 : ℝ) ∂μ) = (μ.mass : ℝ) := by
      simp only [integral_const, smul_eq_mul, mul_one, FiniteMeasure.measureReal_eq_coe_coeFn]
      rfl
    simpa only [kernel_one, ContinuousMap.one_apply, he, Real.sqrt_one, div_one] using hh
  have hbound : ∀ᶠ t : ℝ in atTop, (scaledMeasure ν (positiveScale t)).mass ≤ c + 1 := by
    have hh := hmass.eventually (gt_mem_nhds (by linarith : (c : ℝ) < (c : ℝ) + 1))
    filter_upwards [hh] with t ht
    exact_mod_cast ht.le
  apply tendsto_of_kernel_integrals hbound
  intro a
  rw [kernel_integral_limitMeasure]
  exact tendsto_kernel_scaledMeasure ν hν c hres a

end
end krylov.Strings.Tail
