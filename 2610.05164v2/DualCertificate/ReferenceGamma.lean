import «2610.05164v2».DualCertificate.ReferenceDefect
import «2610.05164v2».Calibration.GlobalMinimum

/-!
Article: 2610.05164v2, Theorem 3.6.
F.1(G): a smooth nonnegative normalized contact coefficient, including its actual value at t=0.
Use: `«2610.05164v2».Calibration.ReferenceData.normalizedGamma_nonneg` feeds
`«2610.05164v2».DualCertificate.Data.normalization_calibration` (normalization calibration).
Proof chain: `«2610.05164v2».DualCertificate.Data.Admissible` — 2610.05164v2, Theorem E.1; Stability
of strict admissibility and uniform transfer of the certificate value.
-/
namespace «2610.05164v2».Calibration.ReferenceData
noncomputable section
open Set Real «2610.05164v2».Calculus «2610.05164v2».DualCertificate
open scoped ContDiff
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable (R : «2610.05164v2».Calibration.ReferenceData) {σ : ℝ} (hσ : 0<σ)

/--
Defines `normalizedDefectQuotient` of type `ℝ → ℝ` by `Classical.choose
(R.normalizedDefect_cubic_quotient hσ)`.

Use: `«2610.05164v2».Calibration.ReferenceData.normalizedGamma` uses this definition in the
displayed construction of `normalizedGamma`. Its inputs and component formulas are fixed by
that definition.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.
-/
def normalizedDefectQuotient : ℝ → ℝ := Classical.choose (R.normalizedDefect_cubic_quotient hσ)

/--
Smoothness to the stated order: `ContDiffOn ℝ ∞ (R.normalizedDefectQuotient hσ) (Icc (0:ℝ) 1)`.

Use: `«2610.05164v2».Calibration.ReferenceData.normalizedDefectQuotient_zero` uses this
assertion to establish the identity `R.normalizedDefectQuotient hσ 0=0`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates
`«2610.05164v2».Calibration.ReferenceData.normalizedDefect_cubic_quotient` with the arguments
shown in the proof.
-/
theorem normalizedDefectQuotient_smooth : ContDiffOn ℝ ∞ (R.normalizedDefectQuotient hσ) (Icc (0:ℝ) 1) :=
  (Classical.choose_spec (R.normalizedDefect_cubic_quotient hσ)).1

/--
Exact identity `R.normalizedDefect hσ t=t^3*R.normalizedDefectQuotient hσ t`.

Use: `«2610.05164v2».Calibration.ReferenceData.normalizedDefectQuotient_zero` uses this
identity to establish the identity `R.normalizedDefectQuotient hσ 0=0`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates
`«2610.05164v2».Calibration.ReferenceData.normalizedDefect_cubic_quotient` with the arguments
shown in the proof.
-/
theorem normalizedDefectQuotient_factor {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    R.normalizedDefect hσ t=t^3*R.normalizedDefectQuotient hσ t :=
  (Classical.choose_spec (R.normalizedDefect_cubic_quotient hσ)).2 t ht

/--
Exact identity `R.normalizedDefectQuotient hσ 0=0`.

Use: `«2610.05164v2».Calibration.ReferenceData.normalizedGamma_zero` rewrites with this
identity to establish the identity `R.normalizedGamma hσ 0=0`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates
`«2610.05164v2».Calibration.ReferenceData.normalizedDefect_order_seven`,
`«2610.05164v2».Calculus.cubic_quotient_zero_of_order_seven`,
`«2610.05164v2».Calibration.ReferenceData.normalizedDefectQuotient_smooth` with the arguments
shown in the proof.
-/
theorem normalizedDefectQuotient_zero : R.normalizedDefectQuotient hσ 0=0 := by
  obtain ⟨C,_,hC⟩ := R.normalizedDefect_order_seven hσ
  exact cubic_quotient_zero_of_order_seven (R.normalizedDefectQuotient_smooth hσ).continuousOn
    (fun t ht => R.normalizedDefectQuotient_factor hσ ht) hC

/--
Defines `normalizedGamma` of type `ℝ` by `(t^3*(2-t^3-R.normalizedReflectedFilter hσ t)+
R.normalizedDefectQuotient hσ t*(2*R.normalizedReflectedFilter hσ t-t^3*(2-t^3)))/
((2-t^3)*(2+σ*(R.normalizedFilter hσ t+R.normalizedReflectedFilter hσ t)))`.

Use: `«2610.05164v2».Calibration.ReferenceData.normalizedGamma_factor` uses this definition to
establish exact identity `(R.calibration hσ hb homega).Gamma (t^3)=Q (t^3)*R.normalizedGamma hσ
t`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.
-/
def normalizedGamma (t : ℝ) : ℝ :=
  (t^3*(2-t^3-R.normalizedReflectedFilter hσ t)+
    R.normalizedDefectQuotient hσ t*(2*R.normalizedReflectedFilter hσ t-t^3*(2-t^3)))/
    ((2-t^3)*(2+σ*(R.normalizedFilter hσ t+R.normalizedReflectedFilter hσ t)))

/--
The stated quantitative bound `0≤R.normalizedReflectedFilter hσ t`.

Use: `«2610.05164v2».Calibration.ReferenceData.normalizedGamma_denominator_positive` uses this
bound to prove the bound `0<(2-t^3)*(2+σ*(R.normalizedFilter hσ
t+R.normalizedReflectedFilter hσ t))`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates `«2610.05164v2».Calibration.ReferenceData.filter_bounds`
with the arguments shown in the proof.
-/
theorem normalizedReflectedFilter_nonneg (t : ℝ) :
    0≤R.normalizedReflectedFilter hσ t := (R.filter_bounds hσ (-R.normalizedX t)).1

/--
The stated quantitative bound `0<(2-t^3)*(2+σ*(R.normalizedFilter hσ
t+R.normalizedReflectedFilter hσ t))`.

Use: `«2610.05164v2».Calibration.ReferenceData.normalizedGamma_factor` uses this bound to
establish exact identity `(R.calibration hσ hb homega).Gamma (t^3)=Q (t^3)*R.normalizedGamma hσ
t`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates `«2610.05164v2».DualCertificate.cube_mem`,
`«2610.05164v2».Calibration.ReferenceData.normalizedFilter_bounds`,
`«2610.05164v2».Calibration.ReferenceData.normalizedReflectedFilter_nonneg` with the arguments
shown in the proof.
-/
theorem normalizedGamma_denominator_positive {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    0<(2-t^3)*(2+σ*(R.normalizedFilter hσ t+R.normalizedReflectedFilter hσ t)) := by
  have hc := cube_mem ht
  have h₁ := (R.normalizedFilter_bounds hσ ht).1
  have h₂ := R.normalizedReflectedFilter_nonneg hσ t
  exact mul_pos (by linarith [hc.2])
    (by nlinarith [mul_nonneg hσ.le (add_nonneg h₁ h₂)])

/--
Smoothness to the stated order: `ContDiffOn ℝ ∞ (R.normalizedGamma hσ) (Icc (0:ℝ) 1)`.

Use: `«2610.05164v2».Calibration.ReferenceData.contactCoreIntegrand_smooth` uses this assertion
to establish smoothness to the stated order: `ContDiffOn ℝ ∞ (R.contactCoreIntegrand hσ) (Icc
(0:ℝ) 1)`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates
`«2610.05164v2».Calibration.ReferenceData.normalizedFilter_smooth`,
`«2610.05164v2».Calibration.ReferenceData.normalizedReflectedFilter_smooth`,
`«2610.05164v2».Calibration.ReferenceData.normalizedDefectQuotient_smooth` with the arguments
shown in the proof.
-/
theorem normalizedGamma_smooth : ContDiffOn ℝ ∞ (R.normalizedGamma hσ) (Icc (0:ℝ) 1) := by
  -- Use the identities/estimates
  -- `«2610.05164v2».Calibration.ReferenceData.normalizedFilter_smooth`,
  -- `«2610.05164v2».Calibration.ReferenceData.normalizedReflectedFilter_smooth`,
  -- `«2610.05164v2».Calibration.ReferenceData.normalizedDefectQuotient_smooth` with the
  -- arguments shown in the proof.
  have ht : ContDiffOn ℝ ∞ (fun t : ℝ => t^3) (Icc 0 1) := by fun_prop
  have hh : ContDiffOn ℝ ∞ (fun t : ℝ => 2-t^3) (Icc 0 1) := contDiffOn_const.sub ht
  have hl := R.normalizedFilter_smooth hσ
  have hr := R.normalizedReflectedFilter_smooth hσ
  exact ((ht.mul (hh.sub hr)).add ((R.normalizedDefectQuotient_smooth hσ).mul
    ((contDiffOn_const.mul hr).sub (ht.mul hh)))).div
      (hh.mul (contDiffOn_const.add (contDiffOn_const.mul (hl.add hr))))
      (fun _ ht => (R.normalizedGamma_denominator_positive hσ ht).ne')

/--
Exact identity `R.normalizedGamma hσ 0=0`.

Use: `«2610.05164v2».Calibration.ReferenceData.normalizedGamma_nonneg` rewrites with this
identity to prove the bound `0≤R.normalizedGamma hσ t`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates
`«2610.05164v2».Calibration.ReferenceData.normalizedDefectQuotient_zero` with the arguments
shown in the proof.
-/
theorem normalizedGamma_zero : R.normalizedGamma hσ 0=0 := by simp [normalizedGamma,R.normalizedDefectQuotient_zero hσ]

/--
Exact identity `(R.calibration hσ hb homega).Gamma (t^3)=Q (t^3)*R.normalizedGamma hσ t`.

Use: `«2610.05164v2».Calibration.ReferenceData.normalizedGamma_nonneg` rewrites with this
identity to prove the bound `0≤R.normalizedGamma hσ t`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Separate `t=0` from its negation; prove the goal under each of these mutually exclusive
hypotheses. Clear the denominators using the available nonzero hypotheses, then verify the
remaining algebraic identity.
-/
theorem normalizedGamma_factor {b omega : ℝ} (hb : 0<b) (homega : 0≤omega)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    (R.calibration hσ hb homega).Gamma (t^3)=Q (t^3)*R.normalizedGamma hσ t := by
  -- Separate `t=0` from its negation; prove the goal under each of these mutually exclusive
  -- hypotheses.
  by_cases hz : t=0
  · simp [hz,Data.Gamma_zero,Q]
  have hp : 0<t := lt_of_le_of_ne ht.1 (Ne.symm hz)
  have hq := Side.q_interior Side.left ⟨hp,ht.2⟩
  change t^3 ∈ Ioo (0:ℝ) 2 at hq
  rw [R.calibration_Gamma_value hσ hb homega hq]
  change (Q (t^3)*(R.normalizedFilter hσ t+R.normalizedReflectedFilter hσ t)-
    2*R.normalizedFilter hσ t*R.normalizedReflectedFilter hσ t)/
    (2+σ*(R.normalizedFilter hσ t+R.normalizedReflectedFilter hσ t))=_
  have hf := R.normalizedDefectQuotient_factor hσ ht
  unfold normalizedDefect at hf
  have hL : R.normalizedFilter hσ t=t^3-t^3*R.normalizedDefectQuotient hσ t := by linarith
  have hden := R.normalizedGamma_denominator_positive hσ ht
  unfold normalizedGamma Q
  have hhead : 0<2-t^3 := by linarith [(cube_mem ht).2]
  have hD : 0<2+σ*(R.normalizedFilter hσ t+R.normalizedReflectedFilter hσ t) :=
    (mul_pos_iff_of_pos_left hhead).mp hden
  field_simp [hhead.ne',hD.ne']
  rw [hL]
  ring

/--
The stated quantitative bound `0≤R.normalizedGamma hσ t`.

Use: `«2610.05164v2».DualCertificate.referenceNormalizedCalibration` uses this bound in the
displayed construction of `referenceNormalizedCalibration`. Its inputs and component formulas
are fixed by that definition.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Separate `t=0` from its negation; prove the goal under each of these mutually exclusive
hypotheses.
-/
theorem normalizedGamma_nonneg {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    0≤R.normalizedGamma hσ t := by
  -- Separate `t=0` from its negation; prove the goal under each of these mutually exclusive
  -- hypotheses.
  by_cases hz : t=0
  · simp [hz,R.normalizedGamma_zero hσ]
  have hp : 0<t := lt_of_le_of_ne ht.1 (Ne.symm hz)
  have hq := Side.q_interior Side.left ⟨hp,ht.2⟩
  change t^3 ∈ Ioo (0:ℝ) 2 at hq
  have h := (R.calibration hσ (show (0:ℝ)<1 by norm_num) (show (0:ℝ)≤0 by norm_num)).Gamma_nonneg
    ⟨hq.1.le,hq.2.le⟩
  rw [R.normalizedGamma_factor hσ (show (0:ℝ)<1 by norm_num) (show (0:ℝ)≤0 by norm_num) ht] at h
  exact nonneg_of_mul_nonneg_right h (Q_positive hq)

end
end «2610.05164v2».Calibration.ReferenceData
