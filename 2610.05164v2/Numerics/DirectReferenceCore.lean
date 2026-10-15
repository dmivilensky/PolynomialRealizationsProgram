import «2610.05164v2».DualCertificate.ReferenceNumericalIntegrands

/-!
Article: 2610.05164v2, Section 4.1.
A value-only reference integrand.
Use: `«2610.05164v2».Calibration.ReferenceData.calibration_constant_direct` feeds
`«2610.05164v2».Certificates.Compact.ReferenceConstant.constant_enclosed` (constant enclosed).
Proof chain: `«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement` —
2610.05164v2, Theorem 1.2, factor 1.000013; Unconditional uniform gain comparison with the retained
numerical factor.
-/
namespace «2610.05164v2».Calibration.ReferenceData
noncomputable section
open Set Real «2610.05164v2».DualCertificate
set_option autoImplicit false
variable (R : ReferenceData) {σ : ℝ} (hσ : 0 < σ)

/--
Defines `directGamma` of type `ℝ` by `((t^3*(2-t^3))*(R.normalizedFilter hσ
t+R.normalizedReflectedFilter hσ t)- 2*R.normalizedFilter hσ t*R.normalizedReflectedFilter hσ
t)/ (2+σ*(R.normalizedFilter hσ t+R.normalizedReflectedFilter hσ t))`.

Use: `«2610.05164v2».Calibration.ReferenceData.directContactCore` uses this definition in the
displayed construction of `directContactCore`. Its inputs and component formulas are fixed by
that definition.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def directGamma (t : ℝ) : ℝ :=
  ((t^3*(2-t^3))*(R.normalizedFilter hσ t+R.normalizedReflectedFilter hσ t)-
    2*R.normalizedFilter hσ t*R.normalizedReflectedFilter hσ t)/
      (2+σ*(R.normalizedFilter hσ t+R.normalizedReflectedFilter hσ t))

/--
Exact identity `R.directGamma hσ t = (t^3*(2-t^3))*R.normalizedGamma hσ t`.

Use: `«2610.05164v2».Calibration.ReferenceData.directContactCore_eq` rewrites with this
identity to establish the identity `R.directContactCore hσ t = R.contactCoreIntegrand hσ t`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem directGamma_eq {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    R.directGamma hσ t = (t^3*(2-t^3))*R.normalizedGamma hσ t := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  have hc := cube_mem ht
  have hhead : 0 < 2-t^3 := by linarith [hc.2]
  have hD : 0 < 2+σ*(R.normalizedFilter hσ t+R.normalizedReflectedFilter hσ t) :=
    (mul_pos_iff_of_pos_left hhead).mp (R.normalizedGamma_denominator_positive hσ ht)
  have hf := R.normalizedDefectQuotient_factor hσ ht
  unfold normalizedDefect at hf
  have hL : R.normalizedFilter hσ t=t^3-t^3*R.normalizedDefectQuotient hσ t := by linarith
  unfold directGamma normalizedGamma
  field_simp [hhead.ne', hD.ne']
  rw [hL]
  ring

/--
Defines `directContactCore` of type `ℝ` by `(2*R.directGamma hσ t-(R.normalizedFilter hσ t)^2-
(R.normalizedReflectedFilter hσ t)^2)*R.normalizedVelocity t`.

Use: `«2610.05164v2».Calibration.ReferenceData.directContactCore_eq` rewrites with this
definition to establish the identity `R.directContactCore hσ t = R.contactCoreIntegrand hσ
t`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def directContactCore (t : ℝ) : ℝ :=
  (2*R.directGamma hσ t-(R.normalizedFilter hσ t)^2-
    (R.normalizedReflectedFilter hσ t)^2)*R.normalizedVelocity t

/--
Exact identity `R.directContactCore hσ t = R.contactCoreIntegrand hσ t`.

Use: `«2610.05164v2».Calibration.ReferenceData.calibration_constant_direct` uses this identity
to establish the identity `(R.calibration hσ hb hω).J 2 = (∫ t in Icc (0 : ℝ) 1,
R.directContactCore hσ t)- vacuumSquare σ (R.normalizedReflectedFilter hσ 0)`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Use the identities/estimates `«2610.05164v2».Calibration.ReferenceData.directGamma_eq`
with the arguments shown in the proof.
-/
theorem directContactCore_eq {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    R.directContactCore hσ t = R.contactCoreIntegrand hσ t := by
  simp only [directContactCore, contactCoreIntegrand, R.directGamma_eq hσ ht]
  ring

/--
Exact identity `(R.calibration hσ hb hω).J 2 = (∫ t in Icc (0 : ℝ) 1, R.directContactCore hσ
t)- vacuumSquare σ (R.normalizedReflectedFilter hσ 0)`.

Use: `«2610.05164v2».Certificates.Compact.ReferenceConstant.constant_enclosed` rewrites with
this identity to establish membership in the specified domain/enclosure:
`AmplitudeValues.calibration.J 2∈Icc (lower:ℝ) (upper:ℝ)`.

Article: 2610.05164v2, Theorem 1.2, retained factor 1.000013 via
`«2610.05164v2».Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Use the identities/estimates
`«2610.05164v2».Calibration.ReferenceData.calibration_constant_normalized`,
`«2610.05164v2».Calibration.ReferenceData.directContactCore_eq` with the arguments shown in the
proof.
-/
theorem calibration_constant_direct {b ω : ℝ} (hb : 0 < b) (hω : 0 ≤ ω) :
    (R.calibration hσ hb hω).J 2 =
      (∫ t in Icc (0 : ℝ) 1, R.directContactCore hσ t)-
        vacuumSquare σ (R.normalizedReflectedFilter hσ 0) := by
  -- Use the identities/estimates
  -- `«2610.05164v2».Calibration.ReferenceData.calibration_constant_normalized`,
  -- `«2610.05164v2».Calibration.ReferenceData.directContactCore_eq` with the arguments shown
  -- in the proof.
  rw [R.calibration_constant_normalized hσ hb hω]
  congr 1
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Icc
  intro t ht
  exact (R.directContactCore_eq hσ ht).symm

end
end «2610.05164v2».Calibration.ReferenceData
