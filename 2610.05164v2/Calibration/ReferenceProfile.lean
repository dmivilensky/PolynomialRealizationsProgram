import «2610.05164v2».Calibration.ReferenceAmplitude

/-!
Article: 2610.05164v2, Proposition 5.
Theorem 3.2's reference is an actual Definition 10 comparison profile.
Use: `«2610.05164v2».Calibration.ReferenceData.profile` feeds
`«2610.05164v2».Calibration.ReferenceData.coordinate_derivative` (coordinate derivative).
Proof chain: `«2610.05164v2».Calibration.ReferenceData.contact_strictMono` — 2610.05164v2, Theorem
3.2; Constructed contact potential and calibrated reference.
-/
namespace «2610.05164v2».Calibration.ReferenceData
noncomputable section
open Set MeasureTheory Filter Real «2610.05164v2».Calibration «2610.05164v2».Comparison
set_option backward.isDefEq.respectTransparency false
variable (R : ReferenceData)

/--
The stated quantitative bound `0 < R.speed q`.

Use: `«2610.05164v2».Calibration.ReferenceData.Q_div_speed_amplitude` uses this bound to
establish the stated quantitative bound `Q q/(R.speed q*R.amplitude q) ≤ 1/(2*R.b 0)`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates `«2610.05164v2».Calibration.Q_positive`,
`«2610.05164v2».Calibration.ReferenceData.speed_gt_two_Q` with the arguments shown in the
proof.
-/
theorem speed_positive {q : ℝ} (hq : q ∈ Ioo (0:ℝ) 2) : 0 < R.speed q :=
  (by linarith [Q_positive hq] : 0 < 2*Q q).trans (R.speed_gt_two_Q hq)

/--
The stated quantitative bound `2/3*R.k*(R.amplitude q)^2 < R.speed q`.

Use: `«2610.05164v2».Calibration.ReferenceData.reciprocal_bound` uses this bound to establish
the stated quantitative bound `(R.speed q)⁻¹ ≤ R.reciprocalConstant*(Q q)^(-(2/3:ℝ))`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates `«2610.05164v2».Calibration.ReferenceData.speed_gt_two_Q`
with the arguments shown in the proof.
-/
theorem speed_gt_two_thirds {q : ℝ} (hq : q ∈ Ioo (0:ℝ) 2) :
    2/3*R.k*(R.amplitude q)^2 < R.speed q := by
  have h := R.speed_gt_two_Q hq
  unfold speed at *
  linarith

/--
The stated quantitative bound `(R.amplitude q)^2/R.speed q ≤ 3/(2*R.k)`.

Use: `«2610.05164v2».Calibration.ReferenceData.profile` uses this bound in the displayed
construction of `profile`. Its inputs and component formulas are fixed by that definition.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates `«2610.05164v2».Calibration.ReferenceData.speed_positive`,
`«2610.05164v2».Calibration.ReferenceData.speed_gt_two_thirds` with the arguments shown in the
proof.
-/
theorem square_div_speed {q : ℝ} (hq : q ∈ Ioo (0:ℝ) 2) :
    (R.amplitude q)^2/R.speed q ≤ 3/(2*R.k) := by
  apply le_of_lt
  apply (div_lt_div_iff₀ (R.speed_positive hq) (by have hk := R.k_positive; positivity)).2
  linarith [R.speed_gt_two_thirds hq]

/--
The stated quantitative bound `Q q/(R.speed q*R.amplitude q) ≤ 1/(2*R.b 0)`.

Use: `«2610.05164v2».Calibration.ReferenceData.profile` uses this bound in the displayed
construction of `profile`. Its inputs and component formulas are fixed by that definition.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates
`«2610.05164v2».Calibration.ReferenceData.amplitude_positive`,
`«2610.05164v2».Calibration.ReferenceData.Q_mem`, `«2610.05164v2».Calibration.Q_positive` with
the arguments shown in the proof.
-/
theorem Q_div_speed_amplitude {q : ℝ} (hq : q ∈ Ioo (0:ℝ) 2) :
    Q q/(R.speed q*R.amplitude q) ≤ 1/(2*R.b 0) := by
  -- Use the identities/estimates
  -- `«2610.05164v2».Calibration.ReferenceData.amplitude_positive`,
  -- `«2610.05164v2».Calibration.ReferenceData.Q_mem`, `«2610.05164v2».Calibration.Q_positive`
  -- with the arguments shown in the proof.
  have hv := R.amplitude_positive hq
  have hb := R.positive 0 (by norm_num)
  have hmono := R.monotone (by norm_num : (0:ℝ) ∈ Icc (0:ℝ) 1)
    (Q_mem ⟨hq.1.le,hq.2.le⟩) (Q_positive hq).le
  have he := R.amplitude_equation ⟨hq.1.le,hq.2.le⟩
  apply (div_le_div_iff₀ (mul_pos (R.speed_positive hq) hv) (by positivity)).2
  have hQ := Q_positive hq
  have hmul := mul_le_mul_of_nonneg_right hmono hQ.le
  unfold speed
  nlinarith

/--
Defines `cubeConstant` of type `ℝ` by `(3*R.root 1+2*R.b 1)/R.k`.

Use: `«2610.05164v2».Calibration.ReferenceData.amplitude_cube_bound` uses this definition to
establish the stated quantitative bound `(R.amplitude q)^3 ≤ R.cubeConstant*Q q`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.
-/
def cubeConstant : ℝ := (3*R.root 1+2*R.b 1)/R.k

/--
The stated quantitative bound `0 < R.cubeConstant`.

Use: a standalone supporting bound for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: 2610.05164v2, Proposition 5.

Proof: Use the identities/estimates `«2610.05164v2».Calibration.ReferenceData.root_spec` with
the arguments shown in the proof.
-/
theorem cubeConstant_positive : 0 < R.cubeConstant := by
  have hν := (R.root_spec (t := 1) (by norm_num)).1
  have hb := R.positive 1 (by norm_num)
  have hk := R.k_positive
  unfold cubeConstant
  positivity

/--
The stated quantitative bound `(R.amplitude q)^3 ≤ R.cubeConstant*Q q`.

Use: `«2610.05164v2».Calibration.ReferenceData.profile` uses this bound in the displayed
construction of `profile`. Its inputs and component formulas are fixed by that definition.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates `«2610.05164v2».Calibration.ReferenceData.Q_mem`,
`«2610.05164v2».Calibration.ReferenceData.root_strictMono`,
`«2610.05164v2».Calibration.ReferenceData.amplitude_equation` with the arguments shown in the
proof.
-/
theorem amplitude_cube_bound {q : ℝ} (hq : q ∈ Icc (0:ℝ) 2) :
    (R.amplitude q)^3 ≤ R.cubeConstant*Q q := by
  -- Use the identities/estimates `«2610.05164v2».Calibration.ReferenceData.Q_mem`,
  -- `«2610.05164v2».Calibration.ReferenceData.root_strictMono`,
  -- `«2610.05164v2».Calibration.ReferenceData.amplitude_equation` with the arguments shown in
  -- the proof.
  have hQ := Q_mem hq
  have hν : R.amplitude q ≤ R.root 1 := R.root_strictMono.monotoneOn hQ (by norm_num) hQ.2
  have hb := R.monotone hQ (by norm_num) hQ.2
  have hνQ := mul_le_mul_of_nonneg_left hν hQ.1
  have hbQ := mul_le_mul_of_nonneg_right hb hQ.1
  have he := R.amplitude_equation hq
  unfold cubeConstant
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ R.k_positive).2
  nlinarith

/--
Defines `reciprocalConstant` of type `ℝ` by `(2/3*R.k*(2*R.b 0/R.k)^(2/3:ℝ))⁻¹`.

Use: `«2610.05164v2».Calibration.ReferenceData.reciprocalConstant_positive` uses this
definition to prove the bound `0 < R.reciprocalConstant`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.
-/
def reciprocalConstant : ℝ := (2/3*R.k*(2*R.b 0/R.k)^(2/3:ℝ))⁻¹

/--
The stated quantitative bound `0 < R.reciprocalConstant`.

Use: a standalone supporting bound for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: 2610.05164v2, Proposition 5.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem reciprocalConstant_positive : 0 < R.reciprocalConstant := by
  have hb := R.positive 0 (by norm_num)
  have hk := R.k_positive
  unfold reciprocalConstant
  positivity

/--
The stated quantitative bound `(R.speed q)⁻¹ ≤ R.reciprocalConstant*(Q q)^(-(2/3:ℝ))`.

Use: `«2610.05164v2».Calibration.ReferenceData.reciprocal_integrable` uses this bound to
establish integrability on the stated domain: `IntegrableOn (fun q => (R.speed q)⁻¹) (Ioo (0:ℝ)
2)`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates
`«2610.05164v2».Calibration.ReferenceData.amplitude_positive`,
`«2610.05164v2».Calibration.Q_positive`, `«2610.05164v2».Calibration.ReferenceData.Q_mem` with
the arguments shown in the proof.
-/
theorem reciprocal_bound {q : ℝ} (hq : q ∈ Ioo (0:ℝ) 2) :
    (R.speed q)⁻¹ ≤ R.reciprocalConstant*(Q q)^(-(2/3:ℝ)) := by
  -- Use the identities/estimates
  -- `«2610.05164v2».Calibration.ReferenceData.amplitude_positive`,
  -- `«2610.05164v2».Calibration.Q_positive`, `«2610.05164v2».Calibration.ReferenceData.Q_mem`
  -- with the arguments shown in the proof.
  have hv := R.amplitude_positive hq
  have hQ := Q_positive hq
  have hk := R.k_positive
  have hb := R.positive 0 (by norm_num)
  have hmono := R.monotone (by norm_num : (0:ℝ) ∈ Icc (0:ℝ) 1)
    (Q_mem ⟨hq.1.le,hq.2.le⟩) hQ.le
  have he := R.amplitude_equation ⟨hq.1.le,hq.2.le⟩
  have hlo : (2*R.b 0/R.k)*Q q ≤ (R.amplitude q)^3 := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hk).2
    nlinarith [mul_le_mul_of_nonneg_right hmono hQ.le]
  have hp := rpow_le_rpow (mul_nonneg (by positivity : 0 ≤ 2*R.b 0/R.k) hQ.le) hlo
    (by norm_num : 0 ≤ (2/3:ℝ))
  have hνpow : ((R.amplitude q)^3)^(2/3:ℝ)=(R.amplitude q)^2 := by
    rw [← rpow_natCast_mul hv.le]
    norm_num
  rw [hνpow,mul_rpow (by positivity : 0 ≤ 2*R.b 0/R.k) hQ.le] at hp
  have hd : (2/3*R.k*(2*R.b 0/R.k)^(2/3:ℝ))*(Q q)^(2/3:ℝ) ≤ R.speed q := by
    have h := mul_le_mul_of_nonneg_left hp (show 0 ≤ 2/3*R.k by positivity)
    linarith [R.speed_gt_two_thirds hq]
  have hp0 : 0 < (2/3*R.k*(2*R.b 0/R.k)^(2/3:ℝ))*(Q q)^(2/3:ℝ) := by positivity
  have h := inv_anti₀ hp0 hd
  simpa only [reciprocalConstant,mul_inv_rev,← rpow_neg hQ.le,mul_comm] using h

/--
Integrability on the stated domain: `IntegrableOn (fun q => (R.speed q)⁻¹) (Ioo (0:ℝ) 2)`.

Use: `«2610.05164v2».Calibration.ReferenceData.profile` uses this integrability result in the
displayed construction of `profile`. Its inputs and component formulas are fixed by that
definition.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem reciprocal_integrable : IntegrableOn (fun q => (R.speed q)⁻¹) (Ioo (0:ℝ) 2) := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  apply (Q_negative_two_thirds_integrable.const_mul R.reciprocalConstant).mono'
  · apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioo
    apply ContinuousOn.inv₀
    · exact (((R.amplitude_continuousOn.mono Ioo_subset_Icc_self).pow 2).const_mul R.k).sub
        (by unfold Q; fun_prop)
    · intro q hq
      exact (R.speed_positive hq).ne'
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with q hq
    rw [Real.norm_of_nonneg (inv_nonneg.mpr (R.speed_positive hq).le)]
    exact R.reciprocal_bound hq

/--
Constructs `profile` of type `Profile R.k` by the displayed record fields. Data fields specify
the construction; proof fields discharge its required properties.

Use: `«2610.05164v2».Calibration.ReferenceData.X_reflection` uses this definition to establish
the precise assertion is `R.referenceSpeed.X (2-q)= -R.referenceSpeed.X q`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.
-/
def profile : Profile R.k where
  amplitude := R.amplitude
  continuous := R.amplitude_continuousOn
  nonneg := fun _ hq => R.amplitude_nonneg hq
  positive := fun _ hq => R.amplitude_positive hq
  speed_positive := fun _ hq => R.speed_positive hq
  reciprocal_integrable := R.reciprocal_integrable
  C := 3/(2*R.k)+1/(2*R.b 0)+R.cubeConstant
  bound := by
    intro q hq
    have h1 := R.square_div_speed hq
    have h2 := R.Q_div_speed_amplitude hq
    have h3 : (R.amplitude q)^3/Q q ≤ R.cubeConstant :=
      (div_le_iff₀ (Q_positive hq)).2 (R.amplitude_cube_bound ⟨hq.1.le,hq.2.le⟩)
    exact add_le_add (add_le_add h1 h2) h3

end
end «2610.05164v2».Calibration.ReferenceData
