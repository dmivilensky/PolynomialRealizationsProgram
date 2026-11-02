import krylov.Strings.TailKernels
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Measure.FiniteMeasure

/-!
Article: main_krylov, apC:prop:tauber, the explicit index-one-half limit.
Use: construct the limiting compact measure from the half-Cauchy density,
so its Stieltjes transform and the two cutoff constants are actual integrals.
Source: the elementary arctangent integral in mathlib; no Tauberian theorem
or preassigned limiting measure is assumed.
-/

namespace krylov.Strings.Tail
noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal

/-- The elementary half-Cauchy density, extended to the whole real line. -/
def halfCauchyDensity (v : ℝ) : ℝ := (2 / Real.pi) * (1 + v ^ 2)⁻¹

/-- The half-Cauchy density is positive and continuous. -/
theorem halfCauchyDensity_pos (v : ℝ) : 0 < halfCauchyDensity v :=
  mul_pos (div_pos (by norm_num) Real.pi_pos) (inv_pos.mpr (by positivity))

/-- The elementary density is continuous on the whole real line. -/
theorem halfCauchyDensity_continuous : Continuous halfCauchyDensity := by
  apply continuous_const.mul
  exact (continuous_const.add (continuous_id.pow 2)).inv₀ (fun v ↦ ne_of_gt (by nlinarith [sq_nonneg v] : (0:ℝ)<1+v^2))

/-- The density is integrable on the positive half-line. -/
theorem halfCauchyDensity_integrable :
    Integrable halfCauchyDensity (volume.restrict (Ioi 0)) :=
  integrable_inv_one_add_sq.integrableOn.const_mul (2 / Real.pi)

/-- The positive half-line has exactly unit half-Cauchy mass. -/
theorem halfCauchyDensity_integral :
    (∫ v in Ioi 0, halfCauchyDensity v) = 1 := by
  change (∫ v in Ioi 0, (2 / Real.pi) * (1 + v ^ 2)⁻¹) = 1
  rw [integral_const_mul, integral_Ioi_inv_one_add_sq]
  simp only [Real.arctan_zero, sub_zero]
  field_simp [Real.pi_ne_zero]

private instance halfCauchy_finite :
    IsFiniteMeasure ((volume.restrict (Ioi (0 : ℝ))).withDensity
      (fun v ↦ ENNReal.ofReal (halfCauchyDensity v))) := by
  apply isFiniteMeasure_withDensity
  rw [← ofReal_integral_eq_lintegral_ofReal halfCauchyDensity_integrable
    (Eventually.of_forall fun v ↦ (halfCauchyDensity_pos v).le), halfCauchyDensity_integral]
  exact ENNReal.ofReal_ne_top

/-- Actual finite half-Cauchy measure on the positive real axis. -/
def halfCauchy : FiniteMeasure ℝ :=
  ⟨(volume.restrict (Ioi (0 : ℝ))).withDensity
    (fun v ↦ ENNReal.ofReal (halfCauchyDensity v)), inferInstance⟩

/-- The elementary rational parametrization of the compactified axis. -/
def cauchyPoint (v : ℝ) : UnitInterval :=
  ⟨1 / (1 + v ^ 2), ⟨by positivity,
    (div_le_one (by positivity : (0 : ℝ) < 1 + v ^ 2)).mpr (by nlinarith [sq_nonneg v])⟩⟩

/-- The half-Cauchy compactification is continuous. -/
theorem cauchyPoint_continuous : Continuous cauchyPoint := by
  apply Continuous.subtype_mk
  exact continuous_const.div (by fun_prop) (fun v ↦ by positivity)

/-- Canonical index-one-half limiting measure on the compact interval. -/
def arcsineMeasure : FiniteMeasure UnitInterval :=
  ⟨(halfCauchy : Measure ℝ).map cauchyPoint, inferInstance⟩

/-- Integration against the explicit limit is integration against its
half-Cauchy parametrization, with no unidentified spectral measure. -/
theorem integral_arcsineMeasure (f : C(UnitInterval, ℝ)) :
    (∫ u, f u ∂arcsineMeasure) =
      ∫ v in Ioi 0, halfCauchyDensity v * f (cauchyPoint v) := by
  change (∫ u, f u ∂(halfCauchy : Measure ℝ).map cauchyPoint) = _
  rw [integral_map cauchyPoint_continuous.measurable.aemeasurable
    f.continuous.aestronglyMeasurable]
  change (∫ v, f (cauchyPoint v) ∂(volume.restrict (Ioi (0 : ℝ))).withDensity _) = _
  rw [integral_withDensity_eq_integral_toReal_smul
    halfCauchyDensity_continuous.measurable.ennreal_ofReal
    (Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (halfCauchyDensity_pos _).le, smul_eq_mul]

/-- The reciprocal quadratic is integrable for every positive parameter. -/
theorem reciprocal_quadratic_integrable (a : PositiveParameter) :
    Integrable (fun v : ℝ ↦ (a + v ^ 2)⁻¹) := by
  have hi := (integrable_inv_one_add_sq.comp_mul_left'
    (inv_ne_zero (Real.sqrt_pos.mpr a.property).ne')).const_mul (a : ℝ)⁻¹
  apply hi.congr
  filter_upwards [] with v
  have hs := Real.sq_sqrt a.property.le
  have hn := (Real.sqrt_pos.mpr a.property).ne'
  generalize hbdef : Real.sqrt (a : ℝ) = b at *
  rw [← hs]
  field_simp [hn]

/-- The positive-real Stieltjes half-power is the elementary arctangent
integral, with its exact normalization. -/
theorem integral_reciprocal_quadratic (a : PositiveParameter) :
    (∫ v in Ioi 0, ((a : ℝ) + v ^ 2)⁻¹) = Real.pi / (2 * Real.sqrt (a : ℝ)) := by
  have hs := Real.sq_sqrt a.property.le
  have hp := Real.sqrt_pos.mpr a.property
  have he : (fun v : ℝ ↦ ((a : ℝ) + v ^ 2)⁻¹) =
      fun v ↦ (a : ℝ)⁻¹ * (1 + ((Real.sqrt (a : ℝ))⁻¹ * v) ^ 2)⁻¹ := by
    funext v
    generalize hbdef : Real.sqrt (a : ℝ) = b at *
    rw [← hs]
    field_simp [hp.ne']
  rw [he, integral_const_mul,
    integral_comp_mul_left_Ioi (fun v : ℝ ↦ (1 + v ^ 2)⁻¹) 0 (inv_pos.mpr hp)]
  simp only [mul_zero, inv_inv, smul_eq_mul, integral_Ioi_inv_one_add_sq,
    Real.arctan_zero, sub_zero]
  generalize hbdef : Real.sqrt (a : ℝ) = b at *
  rw [← hs]
  field_simp [hp.ne']

/-- The explicit compact limiting measure has the required Stieltjes
kernel integrals, including unit mass at the parameter one. -/
theorem kernel_integral_arcsineMeasure (a : PositiveParameter) :
    (∫ u, kernel a u ∂arcsineMeasure) = (Real.sqrt (a : ℝ))⁻¹ := by
  rw [integral_arcsineMeasure]
  have he : (fun v ↦ halfCauchyDensity v * kernel a (cauchyPoint v)) =
      fun v : ℝ ↦ (2 / Real.pi) * ((a : ℝ) + v ^ 2)⁻¹ := by
    funext v
    have hd : (1 : ℝ) + v ^ 2 ≠ 0 := by positivity
    have ha : (a : ℝ) + v ^ 2 ≠ 0 := (add_pos_of_pos_of_nonneg a.property (sq_nonneg v)).ne'
    change (2 / Real.pi) * (1 + v ^ 2)⁻¹ *
      (1 / (1 + ((a : ℝ) - 1) * (1 / (1 + v ^ 2)))) = _
    have hcancel := mul_inv_cancel₀ ha
    field_simp [hd, ha]
    linear_combination hcancel
  rw [he, integral_const_mul, integral_reciprocal_quadratic]
  field_simp [Real.pi_ne_zero, (Real.sqrt_pos.mpr a.property).ne']

end
end krylov.Strings.Tail
