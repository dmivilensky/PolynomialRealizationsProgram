import chebyshev2.Calibration.ChainRule
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
Article: chebyshev2, Theorem 3.2.
Variation of constants for the continuous scalar flows used in Appendix D.
Use: `chebyshev2.Comparison.variation_of_constants` feeds
`chebyshev2.Calibration.ReferenceData.filter_reflection_strict` (filter reflection strict).
Proof chain: `chebyshev2.Calibration.ReferenceData.contact_strictMono` — chebyshev2, Theorem
3.2; Constructed contact potential and calibrated reference.
-/
namespace chebyshev2.Comparison
noncomputable section
open Set MeasureTheory Real chebyshev2.Calibration
set_option backward.isDefEq.respectTransparency false

/--
The precise assertion is `exp (primitive c b)*u b-exp (primitive c a)*u a= ∫ x in a..b, exp
(primitive c x)*e x`.

Use: `chebyshev2.Comparison.variation_of_constants` uses this identity to establish exact
identity `u x=exp (-primitive c x)*(∫ t in a..x, exp (primitive c t)*e t)`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates `chebyshev2.Calibration.primitive_c1`,
`chebyshev2.Calibration.primitive_derivative` with the arguments shown in the proof.
-/
theorem integrating_factor_identity {u c e : ℝ → ℝ} (hc : Continuous c) (he : Continuous e)
    (hu : ∀ x, HasDerivAt u (-c x*u x+e x) x) (a b : ℝ) :
    exp (primitive c b)*u b-exp (primitive c a)*u a=
      ∫ x in a..b, exp (primitive c x)*e x := by
  -- Establish continuity hφ before using the function at limits or in calculus arguments.
  have hφ : Continuous (fun x => exp (primitive c x)*e x) :=
    (Real.continuous_exp.comp (primitive_c1 hc).continuous).mul he
  symm
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ (hφ.intervalIntegrable a b)
  intro x _
  convert! (((primitive_derivative hc x).exp).mul (hu x)) using 1
  ring

/--
Exact identity `u x=exp (-primitive c x)*(∫ t in a..x, exp (primitive c t)*e t)`.

Use: `chebyshev2.Calibration.ReferenceData.contactSlope_integral` uses this identity to
establish the precise assertion is `R.contactSlope hσ x= exp (-primitive (R.contactDamping hσ)
x)* (∫ t in R.referenceSpeed.X 0..x, exp (primitive (R.contactDamping hσ) t)*R.contactForcing
hσ t)`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates `chebyshev2.Comparison.integrating_factor_identity`
with the arguments shown in the proof.
-/
theorem variation_of_constants {u c e : ℝ → ℝ} (hc : Continuous c) (he : Continuous e)
    (hu : ∀ x, HasDerivAt u (-c x*u x+e x) x) {a : ℝ} (h0 : u a=0) (x : ℝ) :
    u x=exp (-primitive c x)*(∫ t in a..x, exp (primitive c t)*e t) := by
  have h := integrating_factor_identity hc he hu a x
  rw [h0,mul_zero,sub_zero] at h
  rw [← h,← mul_assoc,← exp_add,neg_add_cancel,exp_zero,one_mul]

end
end chebyshev2.Comparison
