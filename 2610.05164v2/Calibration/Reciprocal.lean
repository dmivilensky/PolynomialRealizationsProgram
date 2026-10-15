import «2610.05164v2».Calibration.AmplitudeBounds
import «2610.05164v2».PrescribedSpeed.Article
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

/-!
Article: 2610.05164v2, Lemma 10.
Lemma 10's integrable endpoint majorant and the actual comparison density.
Use: `«2610.05164v2».Calibration.Data.comparisonDensity_amplitude` feeds
`«2610.05164v2».Calibration.Data.comparisonDensity_formula` (comparison Density formula).
Proof chain: `«2610.05164v2».Calibration.Data.energy_ge_spectral_bound` — 2610.05164v2, Theorem 3.5;
Pointwise cubic-conjugate criterion, gauge invariance and regular price.
-/
namespace «2610.05164v2».Calibration
noncomputable section
open Set MeasureTheory Real Filter «2610.05164v2».PrescribedSpeed
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/--
Integrability on the stated domain: `IntegrableOn (fun q : ℝ => (Q q)^(-(2/3:ℝ))) (Ioo (0:ℝ)
2)`.

Use: `«2610.05164v2».Calibration.Data.reciprocal_integrable` uses this integrability result to
establish integrability on the stated domain: `IntegrableOn (fun q => (C.speed κ q)⁻¹) (Ioo
(0:ℝ) 2)`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem Q_negative_two_thirds_integrable :
    IntegrableOn (fun q : ℝ => (Q q)^(-(2/3:ℝ))) (Ioo (0:ℝ) 2) := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  have hp : IntervalIntegrable (fun q : ℝ => q^(-(2/3:ℝ))) volume 0 2 :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have hr : IntervalIntegrable (fun q : ℝ => (2-q)^(-(2/3:ℝ))) volume 0 2 := by
    simpa using (hp.comp_sub_left 2).symm
  have hi := ((intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0:ℝ) ≤ 2)).mp hp).add
    ((intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0:ℝ) ≤ 2)).mp hr)
  apply hi.mono'
  · apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioo
    apply ContinuousOn.rpow_const
    · unfold Q
      fun_prop
    · intro q hq
      exact Or.inl (Q_positive hq).ne'
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with q hq
    change ‖(Q q)^(-(2/3:ℝ))‖ ≤ q^(-(2/3:ℝ))+(2-q)^(-(2/3:ℝ))
    rw [Real.norm_of_nonneg (rpow_nonneg (Q_positive hq).le _)]
    rcases le_total q 1 with hq1 | hq1
    · have hQ : q ≤ Q q := by unfold Q; nlinarith [mul_nonneg hq.1.le (sub_nonneg.mpr hq1)]
      exact (rpow_le_rpow_of_nonpos hq.1 hQ (by norm_num)).trans
        (le_add_of_nonneg_right (rpow_nonneg (by linarith [hq.2]) _))
    · have hQ : 2-q ≤ Q q := by
        unfold Q
        nlinarith [mul_nonneg (sub_nonneg.mpr hq.2.le) (sub_nonneg.mpr hq1)]
      exact (rpow_le_rpow_of_nonpos (by linarith [hq.2]) hQ (by norm_num)).trans
        (le_add_of_nonneg_left (rpow_nonneg hq.1.le _))

namespace Data
variable (C : Data)

/--
The stated quantitative bound `(C.speed κ q)⁻¹ ≤ (2/3*κ*(2*C.b/κ)^(2/3:ℝ))⁻¹*(Q q)^(-(2/3:ℝ))`.

Use: `«2610.05164v2».Calibration.Data.reciprocal_integrable` uses this bound to establish
integrability on the stated domain: `IntegrableOn (fun q => (C.speed κ q)⁻¹) (Ioo (0:ℝ) 2)`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates `«2610.05164v2».Calibration.Data.amplitude_spec`,
`«2610.05164v2».Calibration.Q_positive`, `«2610.05164v2».Calibration.Data.amplitude_equation`
with the arguments shown in the proof.
-/
theorem reciprocal_bound {κ q : ℝ} (hκ : 0 < κ) (hq : q ∈ Ioo (0:ℝ) 2) :
    (C.speed κ q)⁻¹ ≤ (2/3*κ*(2*C.b/κ)^(2/3:ℝ))⁻¹*(Q q)^(-(2/3:ℝ)) := by
  -- Use the identities/estimates `«2610.05164v2».Calibration.Data.amplitude_spec`,
  -- `«2610.05164v2».Calibration.Q_positive`,
  -- `«2610.05164v2».Calibration.Data.amplitude_equation` with the arguments shown in the
  -- proof.
  have hv := (C.amplitude_spec hκ hq).1
  have hQ := Q_positive hq
  have hb := C.b_positive
  have he := C.amplitude_equation hκ ⟨hq.1.le,hq.2.le⟩
  have hG := C.Gamma_nonneg ⟨hq.1.le,hq.2.le⟩
  have hw := C.omega_nonneg
  have hlo : (2*C.b/κ)*Q q ≤ (C.amplitude κ q)^3 := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hκ).2
    unfold constant at he
    nlinarith [mul_nonneg (mul_nonneg hκ.le hw) hG]
  have hp := rpow_le_rpow (mul_nonneg (by positivity : 0 ≤ 2*C.b/κ) hQ.le) hlo
    (by norm_num : 0 ≤ (2/3:ℝ))
  have hνpow : ((C.amplitude κ q)^3)^(2/3:ℝ)=(C.amplitude κ q)^2 := by
    rw [← rpow_natCast_mul hv.le]
    norm_num
  rw [hνpow,mul_rpow (by positivity : 0 ≤ 2*C.b/κ) hQ.le] at hp
  have hd : (2/3*κ*(2*C.b/κ)^(2/3:ℝ))*(Q q)^(2/3:ℝ) ≤ C.speed κ q := by
    have h := mul_le_mul_of_nonneg_left hp (show 0 ≤ 2/3*κ by positivity)
    linarith [C.speed_gt_two_thirds hκ hq]
  have hp0 : 0 < (2/3*κ*(2*C.b/κ)^(2/3:ℝ))*(Q q)^(2/3:ℝ) := by positivity
  have h := inv_anti₀ hp0 hd
  simpa only [mul_inv_rev,← rpow_neg hQ.le,mul_comm] using h

/--
Integrability on the stated domain: `IntegrableOn (fun q => (C.speed κ q)⁻¹) (Ioo (0:ℝ) 2)`.

Use: `«2610.05164v2».Calibration.Data.comparisonSpeed` uses this integrability result in the
displayed construction of `comparisonSpeed`. Its inputs and component formulas are fixed by
that definition.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem reciprocal_integrable {κ : ℝ} (hκ : 0 < κ) :
    IntegrableOn (fun q => (C.speed κ q)⁻¹) (Ioo (0:ℝ) 2) := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  apply (Q_negative_two_thirds_integrable.const_mul
    (2/3*κ*(2*C.b/κ)^(2/3:ℝ))⁻¹).mono'
  · apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioo
    apply ContinuousOn.inv₀
    · exact ((continuous_const.continuousOn.mul
        (((C.amplitude_continuousOn_fixed hκ).mono Ioo_subset_Icc_self).pow 2)).sub
          (by unfold Q; fun_prop))
    · intro q hq
      exact (C.speed_positive hκ hq).ne'
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with q hq
    rw [Real.norm_of_nonneg (inv_nonneg.mpr (C.speed_positive hκ hq).le)]
    exact C.reciprocal_bound hκ hq

/--
Definition 6 uses the already proved measurable-speed construction.

Use: `«2610.05164v2».Calibration.Data.comparisonDensity_properties` uses this definition to
establish the integrability result stated in that declaration.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.
-/
def comparisonSpeed {κ : ℝ} (hκ : 0 < κ) : SpeedData where
  D := C.speed κ
  measurable := by
    have he : C.amplitude κ=C.extendedAmplitude κ := by
      funext q
      by_cases hq : q ∈ Icc (0:ℝ) 2
      · exact (C.extendedAmplitude_eq hq).symm
      · have hi : q ∉ Ioo (0:ℝ) 2 := fun hi => hq ⟨hi.1.le,hi.2.le⟩
        rw [amplitude,ite_eq_right hi]
        rcases lt_or_ge q 0 with hl | hl
        · have he : max 0 (min 2 q)=(0:ℝ) := by
            rw [min_eq_right (by linarith),max_eq_left hl.le]
          simp only [extendedAmplitude,he,C.amplitude_zero]
        · have hr : 2 < q := lt_of_not_ge (fun hr => hq ⟨hl,hr⟩)
          have he : max 0 (min 2 q)=(2:ℝ) := by rw [min_eq_left hr.le]; norm_num
          simp only [extendedAmplitude,he,C.amplitude_two]
    unfold speed
    rw [he]
    exact (((C.extendedAmplitude_continuous hκ).pow 2).const_mul κ).measurable.sub
      (by unfold Q; fun_prop)
  positive := fun q hq => C.speed_positive hκ hq
  B := κ*(Classical.choose (C.amplitude_bounded hκ))^2+1
  bound_positive := by positivity
  bound := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with q hq
    have hM := (Classical.choose_spec (C.amplitude_bounded hκ)).2 q ⟨hq.1.le,hq.2.le⟩
    have hp := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (C.amplitude_nonneg hκ q) hM 2) hκ.le
    have hQ := Q_positive hq
    unfold speed
    linarith
  reciprocal_integrable := C.reciprocal_integrable hκ

/--
Defines `comparisonDensity` of type `ℝ → ℝ` by `(C.comparisonSpeed hκ).density κ`.

Use: `«2610.05164v2».Calibration.Data.comparisonDensity_amplitude` rewrites with this
definition to establish the identity `C.comparisonDensity hκ x=(C.amplitude κ
((C.comparisonSpeed hκ).q x))^2`.

Article: 2610.05164v2, Theorem E.1 via
`«2610.05164v2».DualCertificate.Data.packed_value_tendsto`.
-/
def comparisonDensity {κ : ℝ} (hκ : 0 < κ) : ℝ → ℝ := (C.comparisonSpeed hκ).density κ

/--
Integrability of the displayed function: `Integrable (C.comparisonDensity hκ) ∧ (∀ x, 0 ≤
C.comparisonDensity hκ x) ∧ HasCompactSupport (C.comparisonDensity hκ) ∧
«2610.05164v2».GroundState.groundParameter ((C.comparisonSpeed hκ).density_integrable hκ)
((C.comparisonSpeed hκ).density_nonneg hκ)=κ`.

Use: a standalone supporting integrability result for the article chain below; no retained
declaration currently has an explicit proof dependency on it.

Article: 2610.05164v2, Lemma 10.

Proof: Use the identities/estimates
`«2610.05164v2».PrescribedSpeed.SpeedData.density_integrable`,
`«2610.05164v2».PrescribedSpeed.SpeedData.density_nonneg`,
`«2610.05164v2».PrescribedSpeed.SpeedData.density_compact_support` with the arguments shown in
the proof.
-/
theorem comparisonDensity_properties {κ : ℝ} (hκ : 0 < κ) :
    Integrable (C.comparisonDensity hκ) ∧
    (∀ x, 0 ≤ C.comparisonDensity hκ x) ∧ HasCompactSupport (C.comparisonDensity hκ) ∧
    «2610.05164v2».GroundState.groundParameter ((C.comparisonSpeed hκ).density_integrable hκ)
      ((C.comparisonSpeed hκ).density_nonneg hκ)=κ :=
  ⟨(C.comparisonSpeed hκ).density_integrable hκ,(C.comparisonSpeed hκ).density_nonneg hκ,
    (C.comparisonSpeed hκ).density_compact_support κ,(C.comparisonSpeed hκ).groundParameter_density hκ⟩

/--
Exact identity `C.comparisonDensity hκ x=(C.amplitude κ ((C.comparisonSpeed hκ).q x))^2`.

Use: `«2610.05164v2».Calibration.Data.comparisonDensity_formula` uses this identity to
establish exact identity `C.comparisonDensity hκ x=(C.amplitude κ ((C.comparisonSpeed hκ).q
x))^2`.

Article: 2610.05164v2, Theorem E.1 via
`«2610.05164v2».DualCertificate.Data.packed_value_tendsto`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem comparisonDensity_amplitude {κ x : ℝ} (hκ : 0 < κ)
    (hx : x ∈ Ioo ((C.comparisonSpeed hκ).X 0) ((C.comparisonSpeed hκ).X 2)) :
    C.comparisonDensity hκ x=(C.amplitude κ ((C.comparisonSpeed hκ).q x))^2 := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  rw [comparisonDensity,SpeedData.density,indicator_of_mem hx]
  change (C.speed κ ((C.comparisonSpeed hκ).q x)+
    (C.comparisonSpeed hκ).q x*(2-(C.comparisonSpeed hκ).q x))/κ=_
  unfold speed Q
  field_simp
  ring

end Data
end
end «2610.05164v2».Calibration
