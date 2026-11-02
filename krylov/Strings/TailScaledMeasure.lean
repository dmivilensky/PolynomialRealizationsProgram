import krylov.Strings.TailKernels
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
Article: main_krylov, apC:prop:tauber, the actual scaled spectral measures.
Use: construct finite measures on the compact interval directly from the
given spectral measure. Their Stieltjes test integrals are exactly the scaled
positive-real resolvent defects, with no convergence certificate supplied.
Source: pushforward, weighted measures and the explicit compactification
u=t/(t+xi), dmu_t=sqrt(t)*xi/(xi+t) dnu(xi).
-/

namespace krylov.Strings.Tail
noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal

/-- Compactification of the nonnegative spectral variable; the harmless
positive-part extension makes it defined on the whole real line. -/
def compactPoint (t : PositiveParameter) (ξ : ℝ) : UnitInterval :=
  ⟨(t : ℝ) / ((t : ℝ) + max ξ 0), by
    have hd : 0 < (t : ℝ) + max ξ 0 := add_pos_of_pos_of_nonneg t.property (le_max_right _ _)
    exact ⟨div_nonneg t.property.le hd.le, (div_le_one hd).mpr (by linarith [le_max_right ξ 0])⟩⟩

/-- The compactification is an actual continuous map. -/
theorem compactPoint_continuous (t : PositiveParameter) : Continuous (compactPoint t) := by
  apply Continuous.subtype_mk
  exact continuous_const.div (by fun_prop)
    (fun ξ ↦ (add_pos_of_pos_of_nonneg t.property (le_max_right ξ 0)).ne')

/-- Nonnegative weight defining the rescaled spectral measure. -/
def scaledWeight (t : PositiveParameter) (ξ : ℝ) : ℝ :=
  Real.sqrt (t : ℝ) * max ξ 0 / (max ξ 0 + (t : ℝ))

/-- The actual rescaling weight is nonnegative and bounded by sqrt(t). -/
theorem scaledWeight_bounds (t : PositiveParameter) (ξ : ℝ) :
    0 ≤ scaledWeight t ξ ∧ scaledWeight t ξ ≤ Real.sqrt (t : ℝ) := by
  have hd : 0 < max ξ 0 + (t : ℝ) := add_pos_of_nonneg_of_pos (le_max_right _ _) t.property
  constructor
  · exact div_nonneg (mul_nonneg (Real.sqrt_nonneg _) (le_max_right _ _)) hd.le
  · apply (div_le_iff₀ hd).mpr
    nlinarith [mul_nonneg (Real.sqrt_nonneg (t : ℝ)) t.property.le]

/-- The actual rescaling weight is continuous. -/
theorem scaledWeight_continuous (t : PositiveParameter) : Continuous (scaledWeight t) :=
  (continuous_const.mul (continuous_id.max continuous_const)).div (by fun_prop)
    (fun ξ ↦ (add_pos_of_nonneg_of_pos (le_max_right ξ 0) t.property).ne')

/-- Every rescaled weight is integrable for a finite input spectral measure. -/
theorem scaledWeight_integrable (ν : FiniteMeasure ℝ) (t : PositiveParameter) :
    Integrable (scaledWeight t) (ν : Measure ℝ) := by
  apply Integrable.of_bound (scaledWeight_continuous t).aestronglyMeasurable (Real.sqrt (t : ℝ))
  exact Eventually.of_forall fun ξ ↦ by
    rw [Real.norm_of_nonneg (scaledWeight_bounds t ξ).1]
    exact (scaledWeight_bounds t ξ).2

private instance weighted_finite (ν : FiniteMeasure ℝ) (t : PositiveParameter) :
    IsFiniteMeasure ((ν : Measure ℝ).withDensity (fun ξ ↦ ENNReal.ofReal (scaledWeight t ξ))) := by
  apply isFiniteMeasure_withDensity
  rw [← ofReal_integral_eq_lintegral_ofReal (scaledWeight_integrable ν t)
    (Eventually.of_forall fun ξ ↦ (scaledWeight_bounds t ξ).1)]
  exact ENNReal.ofReal_ne_top

/-- The actual finite compact measure used in the Stieltjes continuity proof. -/
def scaledMeasure (ν : FiniteMeasure ℝ) (t : PositiveParameter) : FiniteMeasure UnitInterval :=
  ⟨((ν : Measure ℝ).withDensity (fun ξ ↦ ENNReal.ofReal (scaledWeight t ξ))).map (compactPoint t),
    inferInstance⟩

/-- Integration against the actual scaled measure is its defining weighted
physical spectral integral. -/
theorem integral_scaledMeasure (ν : FiniteMeasure ℝ) (t : PositiveParameter)
    (f : C(UnitInterval, ℝ)) :
    (∫ u, f u ∂scaledMeasure ν t) = ∫ ξ, scaledWeight t ξ * f (compactPoint t ξ) ∂ν := by
  change (∫ u, f u ∂(((ν : Measure ℝ).withDensity
    (fun ξ ↦ ENNReal.ofReal (scaledWeight t ξ))).map (compactPoint t))) = _
  rw [integral_map (compactPoint_continuous t).measurable.aemeasurable
    f.continuous.aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul
      ((scaledWeight_continuous t).measurable.ennreal_ofReal)
      (Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (scaledWeight_bounds t _).1, smul_eq_mul]

/-- A spectral measure carried by nonnegative energies has nonnegative
spectral variable almost everywhere. -/
theorem nonnegative_ae (ν : FiniteMeasure ℝ) (hν : (ν : Measure ℝ) (Iio 0) = 0) :
    ∀ᵐ ξ ∂(ν : Measure ℝ), 0 ≤ ξ := by
  rw [ae_iff]
  simpa only [not_le, Iio] using hν

/-- The compactified Stieltjes integral is exactly the positive-real
resolvent defect at the relative parameter a*t. -/
theorem kernel_integral_scaledMeasure (ν : FiniteMeasure ℝ)
    (hν : (ν : Measure ℝ) (Iio 0) = 0) (t a : PositiveParameter) :
    (∫ u, kernel a u ∂scaledMeasure ν t) =
      Real.sqrt (t : ℝ) * ∫ ξ, ξ / (ξ + (a : ℝ) * t) ∂ν := by
  rw [integral_scaledMeasure, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [nonnegative_ae ν hν] with ξ hξ
  have hd : ξ + (t : ℝ) ≠ 0 := (add_pos_of_nonneg_of_pos hξ t.property).ne'
  have hdt : (t : ℝ) + ξ ≠ 0 := by simpa only [add_comm] using hd
  have hd' : ξ + (a : ℝ) * (t : ℝ) ≠ 0 :=
    (add_pos_of_nonneg_of_pos hξ (mul_pos a.property t.property)).ne'
  have hcomp : 1 + ((a : ℝ) - 1) * ((t : ℝ) / ((t : ℝ) + ξ)) =
      (ξ + (a : ℝ) * t) / (ξ + (t : ℝ)) := by field_simp [hd, hdt]; ring
  change scaledWeight t ξ * (1 / (1 + ((a : ℝ) - 1) *
    ((t : ℝ) / ((t : ℝ) + max ξ 0)))) = _
  rw [max_eq_left hξ]
  dsimp only [scaledWeight]
  rw [max_eq_left hξ, hcomp]
  field_simp [hd, hd']

end
end krylov.Strings.Tail
