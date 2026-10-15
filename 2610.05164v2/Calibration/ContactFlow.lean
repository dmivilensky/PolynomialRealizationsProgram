import «2610.05164v2».Calibration.FilterOrder
import «2610.05164v2».Calibration.ContactAlgebra

/-!
Article: 2610.05164v2, Theorem 3.2.
The contact-parametrized objective and its classical derivative (47).
Use: `«2610.05164v2».Calibration.ReferenceData.calibration_contactFunctional` feeds
`«2610.05164v2».Calibration.ReferenceData.calibration_strict_minimum_lower` (calibration strict
minimum lower).
Proof chain: `«2610.05164v2».Calibration.ReferenceData.calibration_constant_normalized` —
2610.05164v2, Theorem 3.2; Constructed contact potential and calibrated reference.
-/
namespace «2610.05164v2».Calibration.ReferenceData
noncomputable section
open Set MeasureTheory Filter Real
set_option backward.isDefEq.respectTransparency false
variable (R : ReferenceData) {σ : ℝ} (hσ : 0 < σ)

/--
Defines `contactFunctional` of type `ℝ` by `(2*(q-R.contact hσ x)^2-(q^2-2*R.contact hσ
x)*(R.filter hσ x+R.filter hσ (-x)))/ (2+σ*(R.filter hσ x+R.filter hσ (-x)))`.

Use: `«2610.05164v2».Calibration.ReferenceData.calibration_contactFunctional` uses this
definition to establish the identity `(R.calibration hσ hb hω).F q (R.contact hσ
x)=R.contactFunctional hσ q x`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.
-/
def contactFunctional (q x : ℝ) : ℝ :=
  (2*(q-R.contact hσ x)^2-(q^2-2*R.contact hσ x)*(R.filter hσ x+R.filter hσ (-x)))/
    (2+σ*(R.filter hσ x+R.filter hσ (-x)))

/--
Defines `contactDerivative` of type `ℝ` by `2*(q-R.referenceSpeed.q x)/(2+σ*(R.filter hσ
x+R.filter hσ (-x)))* ((1+σ)*(R.filter hσ x-R.filter hσ (-x))*(q-R.referenceSpeed.q x)-
2*contactXi σ (R.referenceSpeed.q x) (R.filter hσ x) (R.filter hσ (-x)))`.

Use: `«2610.05164v2».Calibration.ReferenceData.contactFunctional_derivative` uses this
definition to establish the actual derivative at the stated point: `HasDerivAt
(R.contactFunctional hσ q) (R.contactDerivative hσ q x) x`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.
-/
def contactDerivative (q x : ℝ) : ℝ :=
  2*(q-R.referenceSpeed.q x)/(2+σ*(R.filter hσ x+R.filter hσ (-x)))*
    ((1+σ)*(R.filter hσ x-R.filter hσ (-x))*(q-R.referenceSpeed.q x)-
      2*contactXi σ (R.referenceSpeed.q x) (R.filter hσ x) (R.filter hσ (-x)))

/--
The actual derivative at the stated point: `HasDerivAt (R.contactFunctional hσ q)
(R.contactDerivative hσ q x) x`.

Use: `«2610.05164v2».Calibration.ReferenceData.contactFunctional_continuous` uses this
derivative formula to establish continuity of the displayed function: `Continuous
(R.contactFunctional hσ q)`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates
`«2610.05164v2».Calibration.ReferenceData.coordinate_derivative`,
`«2610.05164v2».Calibration.ReferenceData.filter_derivative`,
`«2610.05164v2».Calibration.ReferenceData.density_reflection` with the arguments shown in the
proof.
-/
theorem contactFunctional_derivative (q x : ℝ) :
    HasDerivAt (R.contactFunctional hσ q) (R.contactDerivative hσ q x) x := by
  -- Use the identities/estimates
  -- `«2610.05164v2».Calibration.ReferenceData.coordinate_derivative`,
  -- `«2610.05164v2».Calibration.ReferenceData.filter_derivative`,
  -- `«2610.05164v2».Calibration.ReferenceData.density_reflection` with the arguments shown in
  -- the proof.
  have hξ := R.coordinate_derivative x
  have hf := R.filter_derivative hσ x
  have hr := (R.filter_derivative hσ (-x)).comp x (hasDerivAt_neg x)
  rw [R.density_reflection] at hr
  have hh := hξ.sub hf
  have hg := hf.add hr
  have hden : 2+σ*(R.filter hσ x+R.filter hσ (-x)) ≠ 0 := by
    have hn := add_nonneg (R.filter_bounds hσ x).1 (R.filter_bounds hσ (-x)).1
    exact ne_of_gt (by positivity)
  have h := ((((hh.const_sub q).pow 2).const_mul 2).sub
    (((hh.const_mul 2).const_sub (q^2)).mul hg)).div
      (hg.const_mul σ |>.const_add 2) hden
  convert! h using 1
  dsimp only [contactDerivative]
  rw [← contact_flow_factorization (M := R.k*R.density x) hden]
  simp only [Pi.add_apply,Pi.sub_apply,Pi.mul_apply,Pi.pow_apply,Function.comp_apply]
  norm_num only [Nat.cast_ofNat,Nat.reduceSub,pow_one]
  ring

/--
Continuity of the displayed function: `Continuous (R.contactFunctional hσ q)`.

Use: `«2610.05164v2».Calibration.ReferenceData.contactFunctional_strictAnti_left` uses this
continuity result to establish `StrictAntiOn (R.contactFunctional hσ
q) (Icc (R.referenceSpeed.X 0) (R.referenceSpeed.X q))`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates
`«2610.05164v2».Calibration.ReferenceData.contactFunctional_derivative` with the arguments
shown in the proof.
-/
theorem contactFunctional_continuous (q : ℝ) : Continuous (R.contactFunctional hσ q) :=
  continuous_iff_continuousAt.mpr (fun x => (R.contactFunctional_derivative hσ q x).continuousAt)

/--
Exact identity `(R.calibration hσ hb hω).F q (R.contact hσ x)=R.contactFunctional hσ q x`.

Use: `«2610.05164v2».Calibration.ReferenceData.calibration_F_reflection` rewrites with this
identity to establish `(R.calibration hσ hb hω).F q (R.contact hσ x)=
(R.calibration hσ hb hω).F (2-q) (R.contact hσ (-x))`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates `«2610.05164v2».Calibration.Data.potential_eq`,
`«2610.05164v2».Calibration.ReferenceData.contact_nonneg`,
`«2610.05164v2».Calibration.ReferenceData.contact_lt_two` with the arguments shown in the
proof.
-/
theorem calibration_contactFunctional {b ω : ℝ} (hb : 0 < b) (hω : 0 ≤ ω)
    (q : ℝ) {x : ℝ} (hx : R.referenceSpeed.X 0 ≤ x) :
    (R.calibration hσ hb hω).F q (R.contact hσ x)=R.contactFunctional hσ q x := by
  -- Use the identities/estimates `«2610.05164v2».Calibration.Data.potential_eq`,
  -- `«2610.05164v2».Calibration.ReferenceData.contact_nonneg`,
  -- `«2610.05164v2».Calibration.ReferenceData.contact_lt_two` with the arguments shown in the
  -- proof.
  unfold Data.F
  rw [(R.calibration hσ hb hω).potential_eq
    ⟨R.contact_nonneg hσ hx,(R.contact_lt_two hσ hx).le⟩]
  change (2*(q-R.contact hσ x)^2-(q^2-2*R.contact hσ x)*R.potential hσ (R.contact hσ x))/
    (2+σ*R.potential hσ (R.contact hσ x))=_
  rw [R.potential_contact hσ hx]
  rfl

end
end «2610.05164v2».Calibration.ReferenceData
