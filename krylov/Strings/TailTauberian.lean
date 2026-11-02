import krylov.Strings.TailScaledLimit
import krylov.Strings.TailScaledCutoffs
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent

/-!
Article: main_krylov, apC:prop:tauber and thm:tail, the Tauberian step.
Use: derive both sharp spectral tails from the real-positive Stieltjes
half-power asymptotic for an actual finite measure supported on [0,infinity).
Source: an explicit compactification proof of the index-one-half Stieltjes
Tauberian theorem: dense resolvent algebra, weak compactness, the elementary
half-Cauchy limit and portmanteau at its null cutoff fibre.  No Karamata,
Krein or Tauberian conclusion is supplied as an axiom or certificate.
-/

namespace krylov.Strings.Tail
noncomputable section
open Set Filter MeasureTheory Asymptotics
open scoped Topology NNReal ENNReal

/-- Continuous weighted cutoffs of the coefficient-scaled limit have the
expected scalar multiple of their elementary half-Cauchy values. -/
theorem setIntegral_limitMeasure (c : ℝ≥0) (h : C(UnitInterval, ℝ)) (E : Set UnitInterval) :
    (∫ u in E, h u ∂limitMeasure c) = (c : ℝ) * ∫ u in E, h u ∂arcsineMeasure := by
  change (∫ u in E, h u ∂((c : ℝ≥0∞) • (arcsineMeasure : Measure UnitInterval))) = _
  rw [Measure.restrict_smul, integral_smul_measure, ENNReal.coe_toReal, smul_eq_mul]

/-- The scaled limit gives zero mass to the moment-cutoff boundary. -/
theorem limitMeasure_moment_frontier_null (c : ℝ≥0) :
    limitMeasure c (frontier momentSet) = 0 := by
  simp only [limitMeasure, FiniteMeasure.smul_apply, arcsineMeasure_moment_frontier_null, smul_zero]

/-- The scaled limit gives zero mass to the tail-cutoff boundary. -/
theorem limitMeasure_tail_frontier_null (c : ℝ≥0) :
    limitMeasure c (frontier tailSet) = 0 := by
  simp only [limitMeasure, FiniteMeasure.smul_apply, arcsineMeasure_tail_frontier_null, smul_zero]

/-- The real-positive Stieltjes half-power law yields the sharp
square-root growth of the truncated first moment of a finite measure. -/
theorem tendsto_moment_div_sqrt (ν : FiniteMeasure ℝ)
    (hν : (ν : Measure ℝ) (Iio 0) = 0) (c : ℝ≥0)
    (hres : Tendsto (fun t : ℝ ↦ Real.sqrt t * ∫ ξ, ξ / (ξ + t) ∂ν)
      atTop (𝓝 (c : ℝ))) :
    Tendsto (fun x : ℝ ↦ (∫ ξ in Ioc 0 x, ξ ∂ν) / Real.sqrt x)
      atTop (𝓝 (2 * (c : ℝ) / Real.pi)) := by
  have hh := tendsto_setIntegral_of_null_frontier (tendsto_scaledMeasure ν hν c hres)
    momentWeight momentWeight_nonneg momentSet_measurable (limitMeasure_moment_frontier_null c)
  rw [setIntegral_limitMeasure, moment_integral_arcsineMeasure,
    show (c : ℝ) * (2 / Real.pi) = 2 * (c : ℝ) / Real.pi by ring] at hh
  apply hh.congr'
  filter_upwards [positiveScale_eventually] with t ht
  rw [moment_integral_scaledMeasure ν hν, ht]

/-- The same real-positive Stieltjes law yields the sharp inverse
square-root decay of the tail mass, including its exact constant. -/
theorem tendsto_sqrt_mul_tail (ν : FiniteMeasure ℝ)
    (hν : (ν : Measure ℝ) (Iio 0) = 0) (c : ℝ≥0)
    (hres : Tendsto (fun t : ℝ ↦ Real.sqrt t * ∫ ξ, ξ / (ξ + t) ∂ν)
      atTop (𝓝 (c : ℝ))) :
    Tendsto (fun x : ℝ ↦ Real.sqrt x * (ν : Measure ℝ).real (Ioi x))
      atTop (𝓝 (2 * (c : ℝ) / Real.pi)) := by
  have hh := tendsto_setIntegral_of_null_frontier (tendsto_scaledMeasure ν hν c hres)
    tailWeight tailWeight_nonneg tailSet_measurable (limitMeasure_tail_frontier_null c)
  rw [setIntegral_limitMeasure, tail_integral_arcsineMeasure,
    show (c : ℝ) * (2 / Real.pi) = 2 * (c : ℝ) / Real.pi by ring] at hh
  apply hh.congr'
  filter_upwards [positiveScale_eventually] with t ht
  rw [tail_integral_scaledMeasure ν hν, ht]

/-- Stieltjes Tauberian theorem at index one half for a genuine finite
nonnegative-energy measure.  The only analytic input is the actual
real-positive resolvent asymptotic; both source tail conclusions follow.
The coefficient may be zero, and a probability normalization is unnecessary. -/
theorem stieltjes_half_tauberian (ν : Measure ℝ) [IsFiniteMeasure ν]
    (hν : ν (Iio 0) = 0) {c : ℝ} (hc : 0 ≤ c)
    (hres : Tendsto (fun t : ℝ ↦ Real.sqrt t * ∫ ξ, ξ / (ξ + t) ∂ν)
      atTop (𝓝 c)) :
    Tendsto (fun x : ℝ ↦ (∫ ξ in Ioc 0 x, ξ ∂ν) / Real.sqrt x)
      atTop (𝓝 (2 * c / Real.pi)) ∧
    Tendsto (fun x : ℝ ↦ Real.sqrt x * ν.real (Ioi x))
      atTop (𝓝 (2 * c / Real.pi)) := by
  exact ⟨tendsto_moment_div_sqrt ⟨ν, inferInstance⟩ hν ⟨c, hc⟩ hres,
    tendsto_sqrt_mul_tail ⟨ν, inferInstance⟩ hν ⟨c, hc⟩ hres⟩

/-- Source-style asymptotic equivalences for both spectral quantities.
Strict positivity of the coefficient is needed only for the ratio-one
notation; the preceding limit theorem also covers a zero coefficient. -/
theorem stieltjes_half_asymptotics (ν : Measure ℝ) [IsFiniteMeasure ν]
    (hν : ν (Iio 0) = 0) {c : ℝ} (hc : 0 < c)
    (hres : Tendsto (fun t : ℝ ↦ Real.sqrt t * ∫ ξ, ξ / (ξ + t) ∂ν)
      atTop (𝓝 c)) :
    (fun x : ℝ ↦ ∫ ξ in Ioc 0 x, ξ ∂ν) ~[atTop]
      (fun x : ℝ ↦ (2 * c / Real.pi) * Real.sqrt x) ∧
    (fun x : ℝ ↦ ν.real (Ioi x)) ~[atTop]
      (fun x : ℝ ↦ (2 * c / Real.pi) / Real.sqrt x) := by
  let A := 2 * c / Real.pi
  have hA : 0 < A := div_pos (mul_pos (by norm_num) hc) Real.pi_pos
  have hlim := stieltjes_half_tauberian ν hν hc.le hres
  have hm : Tendsto (fun x : ℝ ↦ ((∫ ξ in Ioc 0 x, ξ ∂ν) / Real.sqrt x) / A)
      atTop (𝓝 1) := by
    simpa only [A, div_self hA.ne'] using hlim.1.div_const A
  have ht : Tendsto (fun x : ℝ ↦ (Real.sqrt x * ν.real (Ioi x)) / A)
      atTop (𝓝 1) := by
    simpa only [A, div_self hA.ne'] using hlim.2.div_const A
  constructor
  · rw [Asymptotics.isEquivalent_iff_tendsto_one]
    · apply hm.congr'
      filter_upwards [] with x
      simp only [Pi.div_apply]
      ring
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      exact mul_ne_zero hA.ne' (Real.sqrt_pos.mpr hx).ne'
  · rw [Asymptotics.isEquivalent_iff_tendsto_one]
    · apply ht.congr'
      filter_upwards [] with x
      change (Real.sqrt x * ν.real (Ioi x)) / A = ν.real (Ioi x) / (A / Real.sqrt x)
      simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
      ring
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      exact div_ne_zero hA.ne' (Real.sqrt_pos.mpr hx).ne'

end
end krylov.Strings.Tail
