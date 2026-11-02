import krylov.AnalyticTools.PathIntegral
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-!
Article: main_krylov, apC:prop:LV, analyticity at the saddle.
Use: the weighted Volterra operator for the regular-singular slope equation,
as a genuine bounded linear map on continuous paths around zero. Its measure
has density t^(a-1) on (0,1], which is integrable for a>0.
Source: the classical Briot--Bouquet integral construction; integrability of
real powers, compact parametric integration and linear integral bounds in mathlib.
-/

namespace krylov.AnalyticTools
noncomputable section
open Set Filter MeasureTheory

abbrev SymmetricPathDomain := Icc (-1 : ℝ) 1

/-- The actual integrable weight used to invert z d/dz+a. -/
def dilationMeasure (a : ℝ) : Measure ℝ :=
  (volume.restrict (Ioc (0 : ℝ) 1)).withDensity fun t ↦ ENNReal.ofReal (t ^ (a - 1))

theorem dilationMeasure_finite {a : ℝ} (ha : 0 < a) : IsFiniteMeasure (dilationMeasure a) := by
  have hi : IntegrableOn (fun t : ℝ ↦ t ^ (a - 1)) (Ioc 0 1) volume :=
    (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1) (by linarith : -1 < a - 1)).1
  exact isFiniteMeasure_withDensity_ofReal hi.2

/-- Dilation by the unit interval preserves the symmetric compact domain. -/
def unitDilation (u : SymmetricPathDomain) (t : ℝ) : SymmetricPathDomain :=
  ⟨(u : ℝ) * (projIcc 0 1 (by norm_num) t : ℝ), by
    have hq := (projIcc 0 1 (by norm_num : (0 : ℝ) ≤ 1) t).2
    rcases hq with ⟨hq₀, hq₁⟩
    constructor
    · have hh := mul_le_mul_of_nonneg_right u.2.1 hq₀
      nlinarith
    · have hh := mul_le_mul_of_nonneg_right u.2.2 hq₀
      nlinarith⟩

theorem continuous_unitDilation : Continuous (fun p : SymmetricPathDomain × ℝ ↦
    unitDilation p.1 p.2) := by
  unfold unitDilation
  fun_prop

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Weighted averaging over all contractions of an actual continuous path. -/
def weightedDilationMap (a : ℝ) (ha : 0 < a) (f : C(SymmetricPathDomain, E)) :
    C(SymmetricPathDomain, E) where
  toFun u := ∫ t in Icc (0 : ℝ) 1, f (unitDilation u t) ∂dilationMeasure a
  continuous_toFun := by
    let := dilationMeasure_finite ha
    exact continuous_parametric_integral_of_continuous
      (μ := dilationMeasure a) (f := fun u t ↦ f (unitDilation u t))
      (f.continuous.comp continuous_unitDilation) isCompact_Icc

omit [CompleteSpace E] in
theorem norm_weightedDilationMap_le (a : ℝ) (ha : 0 < a)
    (f : C(SymmetricPathDomain, E)) :
    ‖weightedDilationMap a ha f‖ ≤ (dilationMeasure a).real (Icc 0 1) * ‖f‖ := by
  let := dilationMeasure_finite ha
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro u
  change ‖∫ t, f (unitDilation u t) ∂(dilationMeasure a).restrict (Icc 0 1)‖ ≤ _
  have h := norm_integral_le_of_norm_le_const (μ := (dilationMeasure a).restrict (Icc 0 1))
    (C := ‖f‖) (Eventually.of_forall fun t ↦ f.norm_coe_le_norm (unitDilation u t))
  simpa only [Measure.real, Measure.restrict_apply_univ, mul_comm] using h

/-- The weighted Volterra inverse is an actual continuous linear operator. -/
def weightedDilationCLM (a : ℝ) (ha : 0 < a) :
    C(SymmetricPathDomain, E) →L[ℝ] C(SymmetricPathDomain, E) := by
  letI := dilationMeasure_finite ha
  exact LinearMap.mkContinuous
    { toFun := weightedDilationMap a ha
      map_add' := by
        intro f g
        ext u
        exact integral_add
          ((f.continuous.comp (continuous_unitDilation.comp
            (continuous_const.prodMk continuous_id))).integrableOn_Icc)
          ((g.continuous.comp (continuous_unitDilation.comp
            (continuous_const.prodMk continuous_id))).integrableOn_Icc)
      map_smul' := by
        intro c f
        ext u
        exact integral_smul c (fun t ↦ f (unitDilation u t)) }
    ((dilationMeasure a).real (Icc 0 1)) (fun f ↦ by
      change ‖weightedDilationMap a ha f‖ ≤ _
      exact norm_weightedDilationMap_le a ha f)

omit [CompleteSpace E] in
/-- The bounded operator is exactly the printed weighted Volterra integral. -/
theorem weightedDilationCLM_apply (a : ℝ) (ha : 0 < a)
    (f : C(SymmetricPathDomain, E)) (u : SymmetricPathDomain) :
    weightedDilationCLM a ha f u =
      ∫ t in Ioc (0 : ℝ) 1, t ^ (a - 1) • f (unitDilation u t) := by
  change (∫ t in Icc (0 : ℝ) 1, f (unitDilation u t) ∂dilationMeasure a) = _
  have hμ : (dilationMeasure a).restrict (Icc 0 1) = dilationMeasure a := by
    unfold dilationMeasure
    rw [restrict_withDensity measurableSet_Icc,
      Measure.restrict_restrict measurableSet_Icc,
      inter_eq_right.mpr Ioc_subset_Icc_self]
  rw [hμ]
  unfold dilationMeasure
  have hm : Measurable (fun t : ℝ ↦ ENNReal.ofReal (t ^ (a - 1))) :=
    ENNReal.measurable_ofReal.comp (measurable_id.pow_const (a - 1))
  rw [integral_withDensity_eq_integral_toReal_smul hm
    (Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  rw [ENNReal.toReal_ofReal (Real.rpow_nonneg ht.1.le _)]

end
end krylov.AnalyticTools
