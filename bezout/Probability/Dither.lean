import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Algebra.Order.Round
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
Article: bezout, subtractive dither in the distributed ridge model.
Use: the actual rounded quantizer has centered uniform error, independent
of the numerical input, with exact second moment h squared over twelve.
Proof: addition and reflection preserve Haar measure on the unit circle;
its centered representative is uniform on an interval of length one.
-/

namespace bezout.Probability.Dither
noncomputable section
open MeasureTheory Set

/-- The centered unit-length uniform dither law. -/
def law : Measure ℝ := volume.restrict (Ioc (-(1/2:ℝ)) (1/2))

instance : IsProbabilityMeasure law where
  measure_univ := by norm_num [law]

/-- Including both endpoints gives the same uniform law. -/
theorem law_eq_closed : law=volume.restrict (Icc (-(1/2:ℝ)) (1/2)) :=
  restrict_Ioc_eq_restrict_Icc

/-- Centered representative of a phase, with the round-up endpoint convention. -/
def representative (x : AddCircle (1:ℝ)) : ℝ :=
  (AddCircle.equivIoc (1:ℝ) (-(1/2:ℝ)) x).val

/-- Haar phase has the required centered uniform real representative. -/
theorem representative_preserving : MeasurePreserving representative volume law := by
  have h := (measurePreserving_subtype_coe
    (measurableSet_Ioc : MeasurableSet (Ioc (-(1/2:ℝ)) (-(1/2:ℝ)+1)))).comp
    (AddCircle.measurePreserving_equivIoc (T := (1:ℝ)) (a := -(1/2:ℝ)))
  convert h using 1
  · rfl
  · norm_num [law]

/-- The representative of the negative input is exactly its rounding error. -/
theorem representative_neg (x : ℝ) :
    representative ((-x:ℝ) : AddCircle (1:ℝ))=(round x:ℝ)-x := by
  unfold representative AddCircle.equivIoc
  rw [QuotientAddGroup.equivIocMod_coe]
  simp only [toIocMod_eq_sub_fract_mul, div_one, mul_one, Int.fract, round_eq]
  norm_num
  rw [Int.fract]
  ring_nf

/-- Unit-step subtractive quantization error at an arbitrary numerical input. -/
def normalizedError (g u : ℝ) : ℝ := representative ((-(g+u):ℝ) : AddCircle (1:ℝ))

/-- The actual rounded error agrees with the measure-preserving phase construction. -/
theorem normalizedError_eq (g u : ℝ) :
    normalizedError g u=(round (g+u):ℝ)-(g+u) := representative_neg (g+u)

/-- The rounded error is uniform for every input, hence its law is input-independent. -/
theorem normalizedError_preserving (g : ℝ) :
    MeasurePreserving (normalizedError g) law law := by
  have hm : MeasurePreserving ((↑) : ℝ → AddCircle (1:ℝ)) law volume := by
    convert AddCircle.measurePreserving_mk (1:ℝ) (-(1/2:ℝ)) using 1; norm_num [law]
  have hs := (Measure.measurePreserving_neg (volume : Measure (AddCircle (1:ℝ)))).comp
    (measurePreserving_add_left volume (g : AddCircle (1:ℝ)))
  have h := representative_preserving.comp (hs.comp hm)
  convert h using 1
  funext u
  simp only [normalizedError, Function.comp_apply, AddCircle.coe_add, AddCircle.coe_neg]

/-- Mean of the centered unit dither law. -/
theorem integral_id : (∫ u, u ∂law)=0 := by
  rw [law, ← intervalIntegral.integral_of_le (by norm_num : -(1/2:ℝ)≤1/2), _root_.integral_id]
  norm_num

/-- Exact variance of the centered unit dither law. -/
theorem integral_square : (∫ u, u^2 ∂law)=(1/12:ℝ) := by
  rw [law, ← intervalIntegral.integral_of_le (by norm_num : -(1/2:ℝ)≤1/2), integral_pow]
  norm_num

/-- Subtractive quantization with actual nearest-integer rounding. -/
def quantizer (h g u : ℝ) : ℝ := h*((round (g/h+u):ℝ)-u)

/-- The literal quantizer error is its scaled uniform phase error. -/
theorem quantizer_error (h g u : ℝ) (hh : h≠0) :
    quantizer h g u-g=h*normalizedError (g/h) u := by
  rw [normalizedError_eq]
  unfold quantizer
  field_simp
  ring

/-- Subtractive rounding is unbiased at every input. -/
theorem quantizer_unbiased (h g : ℝ) (hh : h≠0) :
    (∫ u, quantizer h g u-g ∂law)=0 := by
  simp_rw [quantizer_error h g _ hh]
  rw [integral_const_mul]
  have he := (integral_map (normalizedError_preserving (g/h)).measurable.aemeasurable
    (by fun_prop : AEStronglyMeasurable (fun u : ℝ => u)
      (Measure.map (normalizedError (g/h)) law))).symm
  rw [(normalizedError_preserving (g/h)).map_eq] at he
  simpa only [integral_id, mul_zero] using congrArg (fun t : ℝ => h*t) he

/-- Every input has the exact quantization-error variance h squared over twelve. -/
theorem quantizer_variance (h g : ℝ) (hh : h≠0) :
    (∫ u, (quantizer h g u-g)^2 ∂law)=h^2/12 := by
  simp_rw [quantizer_error h g _ hh, mul_pow]
  rw [integral_const_mul]
  have he := (integral_map (normalizedError_preserving (g/h)).measurable.aemeasurable
    (by fun_prop : AEStronglyMeasurable (fun u : ℝ => u^2)
      (Measure.map (normalizedError (g/h)) law))).symm
  rw [(normalizedError_preserving (g/h)).map_eq] at he
  rw [he, integral_square]
  ring

end
end bezout.Probability.Dither
