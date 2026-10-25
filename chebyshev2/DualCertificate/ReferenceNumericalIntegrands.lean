import chebyshev2.DualCertificate.ReferenceGamma
import chebyshev2.Calibration.CalibrationConstant
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
Article: chebyshev2, Theorem 3.2.
The actual compact reference integrand used for B_star in Table 2.
Use: `chebyshev2.Calibration.ReferenceData.calibration_constant_normalized` feeds
`chebyshev2.Numerics.ReferenceCoreSource.calibration_constant_enclosed` (calibration constant
enclosed).
-/
namespace chebyshev2.Calibration.ReferenceData
noncomputable section
open Set MeasureTheory Real chebyshev2.DualCertificate
open scoped ContDiff
set_option autoImplicit false
set_option maxHeartbeats 2000000
variable (R : ReferenceData) {σ : ℝ} (hσ : 0<σ)

/--
Defines `contactCoreIntegrand` of type `ℝ` by `(2*(t^3*(2-t^3))*R.normalizedGamma hσ t-
(R.normalizedFilter hσ t)^2-(R.normalizedReflectedFilter hσ t)^2)*R.normalizedVelocity t`.

Use: `chebyshev2.Calibration.ReferenceData.calibration_constant_normalized` rewrites with
this definition to establish `(R.calibration hσ hb ho).J 2= (∫ t in
Icc (0:ℝ) 1,R.contactCoreIntegrand hσ t)- vacuumSquare σ (R.normalizedReflectedFilter hσ 0)`.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def contactCoreIntegrand (t : ℝ) : ℝ :=
  (2*(t^3*(2-t^3))*R.normalizedGamma hσ t-
    (R.normalizedFilter hσ t)^2-(R.normalizedReflectedFilter hσ t)^2)*R.normalizedVelocity t

/--
Defines `vacuumSquare` of type `ℝ` by `(σ*w-2*log (1+σ*w/2))/σ^2`.

Use: `chebyshev2.Calibration.ReferenceData.calibration_constant_normalized` uses this
definition to establish `(R.calibration hσ hb ho).J 2= (∫ t in Icc
(0:ℝ) 1,R.contactCoreIntegrand hσ t)- vacuumSquare σ (R.normalizedReflectedFilter hσ 0)`.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def vacuumSquare (σ w : ℝ) : ℝ := (σ*w-2*log (1+σ*w/2))/σ^2

/--
Smoothness to the stated order: `ContDiffOn ℝ ∞ (R.contactCoreIntegrand hσ) (Icc (0:ℝ) 1)`.

Use: `chebyshev2.Certificates.Compact.ContactValues.contact_integral_error` uses this
assertion to establish the identity stated in that declaration.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Use the identities/estimates
`chebyshev2.Calibration.ReferenceData.normalizedGamma_smooth`,
`chebyshev2.Calibration.ReferenceData.normalizedFilter_smooth`,
`chebyshev2.Calibration.ReferenceData.normalizedReflectedFilter_smooth` with the arguments
shown in the proof.
-/
theorem contactCoreIntegrand_smooth :
    ContDiffOn ℝ ∞ (R.contactCoreIntegrand hσ) (Icc (0:ℝ) 1) := by
  have hp : ContDiffOn ℝ ∞ (fun t : ℝ => 2*(t^3*(2-t^3))) (Icc 0 1) := by fun_prop
  exact (((hp.mul (R.normalizedGamma_smooth hσ)).sub
    ((R.normalizedFilter_smooth hσ).pow 2)).sub
    ((R.normalizedReflectedFilter_smooth hσ).pow 2)).mul R.normalizedVelocity_smooth

/--
The precise assertion is `(∫ x in R.referenceSpeed.X 0..0,f x)= ∫ t in Icc (0:ℝ) 1,f
(R.normalizedX t)*R.normalizedVelocity t`.

Use: `chebyshev2.Calibration.ReferenceData.calibration_constant_normalized` rewrites with
this identity to establish `(R.calibration hσ hb ho).J 2= (∫ t in Icc
(0:ℝ) 1,R.contactCoreIntegrand hσ t)- vacuumSquare σ (R.normalizedReflectedFilter hσ 0)`.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Use the identities/estimates
`chebyshev2.Calibration.ReferenceData.normalizedX_continuous`,
`chebyshev2.Calibration.ReferenceData.normalizedX_derivative`,
`chebyshev2.Calibration.ReferenceData.normalizedSpeed_positive` with the arguments shown in
the proof.
-/
theorem normalized_compact_integral (f : ℝ → ℝ) :
    (∫ x in R.referenceSpeed.X 0..0,f x)=
      ∫ t in Icc (0:ℝ) 1,f (R.normalizedX t)*R.normalizedVelocity t := by
  -- Use the identities/estimates
  -- `chebyshev2.Calibration.ReferenceData.normalizedX_continuous`,
  -- `chebyshev2.Calibration.ReferenceData.normalizedX_derivative`,
  -- `chebyshev2.Calibration.ReferenceData.normalizedSpeed_positive` with the arguments
  -- shown in the proof.
  have h := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (f := R.normalizedX) (f' := R.normalizedVelocity) (g := f) (a := 0) (b := 1)
    R.normalizedX_continuous.continuousOn
    (fun t ht => R.normalizedX_derivative (by
      simpa only [min_eq_left zero_le_one,max_eq_right zero_le_one] using ht))
    (fun t ht => div_nonneg (by norm_num : (0:ℝ)≤3) (R.normalizedSpeed_positive
      (by simpa only [min_eq_left zero_le_one,max_eq_right zero_le_one] using
        (show t∈Icc (min (0:ℝ) 1) (max (0:ℝ) 1) from ⟨ht.1.le,ht.2.le⟩))).le)
  have hz : R.normalizedX 0=R.referenceSpeed.X 0 := by simp [normalizedX]
  have ho : R.normalizedX 1=0 := by simp [normalizedX,R.X_one]
  rw [hz,ho] at h
  rw [←h,intervalIntegral.integral_of_le zero_le_one,←integral_Icc_eq_integral_Ioc]
  rfl

/--
Exact identity `R.normalizedReflectedFilter hσ 0=R.filter hσ (R.referenceSpeed.X 2)`.

Use: `chebyshev2.Calibration.ReferenceData.calibration_constant_normalized` rewrites with
this identity to establish `(R.calibration hσ hb ho).J 2= (∫ t in Icc
(0:ℝ) 1,R.contactCoreIntegrand hσ t)- vacuumSquare σ (R.normalizedReflectedFilter hσ 0)`.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Use the identities/estimates `chebyshev2.Calibration.ReferenceData.X_reflection`
with the arguments shown in the proof.
-/
theorem normalizedReflectedFilter_zero :
    R.normalizedReflectedFilter hσ 0=R.filter hσ (R.referenceSpeed.X 2) := by
  have hr := R.X_reflection 0
  norm_num only [sub_zero] at hr
  simp only [normalizedReflectedFilter,normalizedX,zero_pow (by decide : 3≠0)]
  rw [←hr]

/--
The precise assertion is `(R.calibration hσ hb ho).J 2= (∫ t in Icc (0:ℝ)
1,R.contactCoreIntegrand hσ t)- vacuumSquare σ (R.normalizedReflectedFilter hσ 0)`.

Use: `chebyshev2.Calibration.ReferenceData.calibration_constant_direct` rewrites with this
identity to establish the identity `(R.calibration hσ hb hω).J 2 = (∫ t in Icc (0 : ℝ) 1,
R.directContactCore hσ t)- vacuumSquare σ (R.normalizedReflectedFilter hσ 0)`.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Use the identities/estimates
`chebyshev2.Calibration.ReferenceData.calibration_constant`,
`chebyshev2.Calibration.ReferenceData.normalized_compact_integral`,
`chebyshev2.Calibration.ReferenceData.normalizedReflectedFilter_zero` with the arguments
shown in the proof.
-/
theorem calibration_constant_normalized {b omega : ℝ} (hb : 0<b) (ho : 0≤omega) :
    (R.calibration hσ hb ho).J 2=
      (∫ t in Icc (0:ℝ) 1,R.contactCoreIntegrand hσ t)-
        vacuumSquare σ (R.normalizedReflectedFilter hσ 0) := by
  -- Use the identities/estimates
  -- `chebyshev2.Calibration.ReferenceData.calibration_constant`,
  -- `chebyshev2.Calibration.ReferenceData.normalized_compact_integral`,
  -- `chebyshev2.Calibration.ReferenceData.normalizedReflectedFilter_zero` with the
  -- arguments shown in the proof.
  rw [R.calibration_constant hσ hb ho,R.normalized_compact_integral,
    R.normalizedReflectedFilter_zero hσ]
  congr 1
  apply setIntegral_congr_fun measurableSet_Icc
  intro t ht
  have hq : t^3∈Icc (0:ℝ) 2 := ⟨(cube_mem ht).1,(cube_mem ht).2.trans (by norm_num)⟩
  change (2*(R.calibration hσ hb ho).Gamma (R.referenceSpeed.q (R.referenceSpeed.X (t^3)))-
    (R.filter hσ (R.normalizedX t))^2-(R.filter hσ (-R.normalizedX t))^2)*R.normalizedVelocity t=_
  rw [R.referenceSpeed.q_X hq,R.normalizedGamma_factor hσ hb ho ht]
  simp only [contactCoreIntegrand,normalizedFilter,normalizedReflectedFilter,chebyshev2.Calibration.Q]
  ring

end
end chebyshev2.Calibration.ReferenceData
