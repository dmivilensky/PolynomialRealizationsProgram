import chebyshev2.DualCertificate.ReferenceNormalization
import chebyshev2.Calibration.ReferenceContact
import chebyshev2.Calculus.ClosedInterval
import Mathlib.Analysis.ODE.PicardLindelof

/-!
Article: chebyshev2, Section 4.1.
F.1(R): the actual reference space coordinate has the regular normalized velocity 3/d, including
both ends of the closed half interval.
Use: `chebyshev2.Calibration.ReferenceData.normalizedX_derivative_closed` feeds
`chebyshev2.Calibration.ReferenceData.normalizedFilter_derivative` (normalized Filter
derivative).
Proof chain: `chebyshev2.DualCertificate.Data.Admissible` — chebyshev2, Theorem E.1; Stability
of strict admissibility and uniform transfer of the certificate value.
-/
namespace chebyshev2.Calibration.ReferenceData
noncomputable section
open Set Real chebyshev2.DualCertificate
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable (R : chebyshev2.Calibration.ReferenceData)

/--
Defines `normalizedX` of type `ℝ` by `R.referenceSpeed.X (t^3)`.

Use: `chebyshev2.Calibration.ReferenceData.normalizedX_derivative` uses this definition to
establish the actual derivative at the stated point: `HasDerivAt R.normalizedX
(R.normalizedVelocity t) t`.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def normalizedX (t : ℝ) : ℝ := R.referenceSpeed.X (t^3)
/--
Defines `normalizedVelocity` of type `ℝ` by `3/R.normalizedSpeed t`.

Use: `chebyshev2.Calibration.ReferenceData.normalizedX_derivative` uses this definition to
establish the actual derivative at the stated point: `HasDerivAt R.normalizedX
(R.normalizedVelocity t) t`.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.
-/
def normalizedVelocity (t : ℝ) : ℝ := 3/R.normalizedSpeed t

/--
Smoothness to the stated order: `ContDiffOn ℝ ∞ R.normalizedVelocity (Icc (0:ℝ) 1)`.

Use: `chebyshev2.Calibration.ReferenceData.normalizedX_derivative_closed` uses this
assertion to establish the derivative within the stated domain: `HasDerivWithinAt R.normalizedX
(R.normalizedVelocity t) (Icc (0:ℝ) 1) t`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates
`chebyshev2.Calibration.ReferenceData.normalizedSpeed_smooth`,
`chebyshev2.Calibration.ReferenceData.normalizedSpeed_positive` with the arguments shown in
the proof.
-/
theorem normalizedVelocity_smooth : ContDiffOn ℝ ∞ R.normalizedVelocity (Icc (0:ℝ) 1) :=
  contDiffOn_const.div R.normalizedSpeed_smooth
    (fun _ ht => (R.normalizedSpeed_positive ht).ne')

/--
Continuity of the displayed function: `Continuous R.normalizedX`.

Use: `chebyshev2.Calibration.ReferenceData.normalizedX_derivative_closed` uses this
continuity result to establish the derivative within the stated domain: `HasDerivWithinAt
R.normalizedX (R.normalizedVelocity t) (Icc (0:ℝ) 1) t`.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Use the identities/estimates `chebyshev2.PrescribedSpeed.SpeedData.X_continuous`
with the arguments shown in the proof.
-/
theorem normalizedX_continuous : Continuous R.normalizedX :=
  R.referenceSpeed.X_continuous.comp (by fun_prop)

/--
The actual derivative at the stated point: `HasDerivAt R.normalizedX (R.normalizedVelocity t)
t`.

Use: `chebyshev2.Calibration.ReferenceData.normalizedX_derivative_closed` uses this
derivative formula to establish the derivative within the stated domain: `HasDerivWithinAt
R.normalizedX (R.normalizedVelocity t) (Icc (0:ℝ) 1) t`.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem normalizedX_derivative {t : ℝ} (ht : t ∈ Ioo (0:ℝ) 1) :
    HasDerivAt R.normalizedX (R.normalizedVelocity t) t := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  have hq := Side.q_interior Side.left ⟨ht.1,ht.2.le⟩
  change t^3 ∈ Ioo (0:ℝ) 2 at hq
  have hcube : HasDerivAt (fun t : ℝ => t^3) (3*t^2) t := by
    convert! (hasDerivAt_id t).pow 3 using 1; norm_num
  have h := (R.profile.X_derivative R.k_positive hq).comp (h := fun t : ℝ => t^3) t hcube
  have hspeed : R.profile.speed (t^3)=R.speed (t^3) :=
    R.profile.speed_eq ⟨hq.1.le,hq.2.le⟩
  rw [hspeed] at h
  change HasDerivAt R.normalizedX ((R.speed (t^3))⁻¹*(3*t^2)) t at h
  rw [R.normalizedSpeed_factor ⟨ht.1.le,ht.2.le⟩] at h
  convert! h using 1
  unfold normalizedVelocity
  field_simp [ht.1.ne',(R.normalizedSpeed_positive ⟨ht.1.le,ht.2.le⟩).ne']

/--
The derivative within the stated domain: `HasDerivWithinAt R.normalizedX (R.normalizedVelocity
t) (Icc (0:ℝ) 1) t`.

Use: `chebyshev2.Calibration.ReferenceData.normalizedFilter_derivative` uses this
derivative formula to establish the derivative within the stated domain: `HasDerivWithinAt
(R.normalizedFilter hσ) (R.normalizedVelocity t*(R.k*(t*R.normalizedRoot t)^2-
2*R.normalizedFilter hσ t-σ*(R.normalizedFilter hσ t)^2)) (Icc (0:ℝ) 1) t`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates
`chebyshev2.Calculus.hasDerivWithinAt_Icc_of_continuous_derivative`,
`chebyshev2.Calibration.ReferenceData.normalizedX_continuous`,
`chebyshev2.Calibration.ReferenceData.normalizedVelocity_smooth` with the arguments shown
in the proof.
-/
theorem normalizedX_derivative_closed {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    HasDerivWithinAt R.normalizedX (R.normalizedVelocity t) (Icc (0:ℝ) 1) t :=
  chebyshev2.Calculus.hasDerivWithinAt_Icc_of_continuous_derivative (by norm_num)
    R.normalizedX_continuous.continuousOn R.normalizedVelocity_smooth.continuousOn
    (fun _ ht => R.normalizedX_derivative ht) t ht

/--
Smoothness to the stated order: `ContDiffOn ℝ ∞ R.normalizedX (Icc (0:ℝ) 1)`.

Use: a standalone supporting assertion for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Section 4.1.

Proof: Use the identities/estimates
`chebyshev2.Calculus.contDiffOn_Icc_of_smooth_derivative`,
`chebyshev2.Calibration.ReferenceData.normalizedX_continuous`,
`chebyshev2.Calibration.ReferenceData.normalizedVelocity_smooth` with the arguments shown
in the proof.
-/
theorem normalizedX_smooth : ContDiffOn ℝ ∞ R.normalizedX (Icc (0:ℝ) 1) :=
  chebyshev2.Calculus.contDiffOn_Icc_of_smooth_derivative (by norm_num)
    R.normalizedX_continuous.continuousOn R.normalizedVelocity_smooth
    (fun _ ht => R.normalizedX_derivative ht)

end
end chebyshev2.Calibration.ReferenceData
