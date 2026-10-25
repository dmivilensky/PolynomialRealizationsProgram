import chebyshev2.Calibration.ContactFlow

/-!
Article: chebyshev2, Theorem 3.2.
Strict derivative signs for the contact objective on 0 < q <= 1.
Use: `chebyshev2.Calibration.ReferenceData.contactDerivative_positive` feeds
`chebyshev2.Calibration.ReferenceData.contactFunctional_strictMono_right` (contact Functional
strict Mono right).
Proof chain: `chebyshev2.Calibration.ReferenceData.calibration_Gamma` — chebyshev2, Theorem
3.2; Constructed contact potential and calibrated reference.
-/
namespace chebyshev2.Calibration.ReferenceData
noncomputable section
open Set Real
set_option backward.isDefEq.respectTransparency false
variable (R : ReferenceData) {σ : ℝ} (hσ : 0 < σ)

/--
The stated quantitative bound `0 < R.referenceSpeed.X 2`.

Use: `chebyshev2.Calibration.ReferenceData.filter_order_coordinate` uses this bound to
establish the stated quantitative bound `(R.referenceSpeed.q x < 1 → R.filter hσ x < R.filter
hσ (-x)) ∧ (1 ≤ R.referenceSpeed.q x → R.filter hσ (-x) ≤ R.filter hσ x)`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates `chebyshev2.Calibration.ReferenceData.X_reflection`,
`chebyshev2.Calibration.ReferenceData.X_zero_negative` with the arguments shown in the
proof.
-/
theorem X_two_positive : 0 < R.referenceSpeed.X 2 := by
  have h := R.X_reflection 0
  norm_num only [sub_zero] at h
  linarith [R.X_zero_negative]

/--
The stated quantitative bound `0 < R.filter hσ x`.

Use: `chebyshev2.Calibration.ReferenceData.contactDerivative_positive` uses this bound to
establish the stated quantitative bound `0 < R.contactDerivative hσ q x`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.

Proof: Assume the failure of the desired conclusion and derive a contradiction from the
available bounds/identities.
-/
theorem filter_positive {x : ℝ} (hx : R.referenceSpeed.X 0 < x) : 0 < R.filter hσ x := by
  -- Assume the failure of the desired conclusion and derive a contradiction from the available
  -- bounds/identities.
  have hs := R.contactSlope_positive hσ hx
  have hQ := Q_nonneg (R.referenceSpeed.q_mem x)
  have hf := (R.filter_bounds hσ x).1
  change 0 < 2*R.filter hσ x+σ*(R.filter hσ x)^2-Q (R.referenceSpeed.q x) at hs
  by_contra h
  have hz : R.filter hσ x=0 := le_antisymm (not_lt.mp h) hf
  rw [hz] at hs
  nlinarith

/--
The stated quantitative bound `(R.referenceSpeed.q x < 1 → R.filter hσ x < R.filter hσ (-x)) ∧
(1 ≤ R.referenceSpeed.q x → R.filter hσ (-x) ≤ R.filter hσ x)`.

Use: `chebyshev2.Calibration.ReferenceData.contact_bracket_negative_interior` uses this
bound to prove the bound `(1+σ)*(R.filter hσ x-R.filter hσ
(-x))*(q-R.referenceSpeed.q x)- 2*contactXi σ (R.referenceSpeed.q x) (R.filter hσ x) (R.filter
hσ (-x)) < 0`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.

Proof: Assume the failure of the desired conclusion and derive a contradiction from the
available bounds/identities.
-/
theorem filter_order_coordinate {x : ℝ}
    (hx : x ∈ Ioo (R.referenceSpeed.X 0) (R.referenceSpeed.X 2)) :
    (R.referenceSpeed.q x < 1 → R.filter hσ x < R.filter hσ (-x)) ∧
    (1 ≤ R.referenceSpeed.q x → R.filter hσ (-x) ≤ R.filter hσ x) := by
  -- Assume the failure of the desired conclusion and derive a contradiction from the available
  -- bounds/identities.
  have h0 : (0:ℝ) ∈ Icc (R.referenceSpeed.X 0) (R.referenceSpeed.X 2) :=
    ⟨R.X_zero_negative.le,R.X_two_positive.le⟩
  constructor
  · intro hq
    have hneg : x < 0 := by
      by_contra h
      have hl := R.coordinate_strictMono.monotoneOn h0 ⟨hx.1.le,hx.2.le⟩ (not_lt.mp h)
      rw [R.coordinate_zero] at hl
      linarith
    exact R.filter_reflection_strict hσ ⟨hx.1,hneg⟩
  · intro hq
    have hpos : 0 ≤ x := by
      by_contra h
      have hl := R.coordinate_strictMono ⟨hx.1.le,hx.2.le⟩ h0 (not_le.mp h)
      rw [R.coordinate_zero] at hl
      linarith
    rcases eq_or_lt_of_le hpos with he | hp
    · subst x
      simp
    · have hr := R.X_reflection 0
      norm_num only [sub_zero] at hr
      exact (R.filter_reflection_strict hσ (x := -x) ⟨by linarith [hx.2],by linarith⟩).le
        |>.trans_eq (by simp)

/--
The stated quantitative bound `(1+σ)*(R.filter hσ x-R.filter hσ (-x))*(q-R.referenceSpeed.q x)-
2*contactXi σ (R.referenceSpeed.q x) (R.filter hσ x) (R.filter hσ (-x)) < 0`.

Use: `chebyshev2.Calibration.ReferenceData.contactDerivative_negative` uses this bound to
establish the stated quantitative bound `R.contactDerivative hσ q x < 0`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates
`chebyshev2.Calibration.ReferenceData.coordinate_interior`,
`chebyshev2.Calibration.ReferenceData.filter_bounds`,
`chebyshev2.Calibration.ReferenceData.contactSlope_positive` with the arguments shown in
the proof.
-/
theorem contact_bracket_negative_interior {q x : ℝ} (hq : q ∈ Ioc (0:ℝ) 1)
    (hx : x ∈ Ioo (R.referenceSpeed.X 0) (R.referenceSpeed.X 2))
    (hh : R.contact hσ x ≤ q) :
    (1+σ)*(R.filter hσ x-R.filter hσ (-x))*(q-R.referenceSpeed.q x)-
      2*contactXi σ (R.referenceSpeed.q x) (R.filter hσ x) (R.filter hσ (-x)) < 0 := by
  -- Use the identities/estimates
  -- `chebyshev2.Calibration.ReferenceData.coordinate_interior`,
  -- `chebyshev2.Calibration.ReferenceData.filter_bounds`,
  -- `chebyshev2.Calibration.ReferenceData.contactSlope_positive` with the arguments shown
  -- in the proof.
  have hξ := R.coordinate_interior hx
  have hf := R.filter_bounds hσ x
  have hr := R.filter_bounds hσ (-x)
  have hs := R.contactSlope_positive hσ hx.1
  have hX := R.X_reflection 0
  norm_num only [sub_zero] at hX
  have ht := R.contactSlope_positive hσ (x := -x) (by linarith [hx.2])
  change 0 < 2*R.filter hσ x+σ*(R.filter hσ x)^2-Q (R.referenceSpeed.q x) at hs
  change 0 < 2*R.filter hσ (-x)+σ*(R.filter hσ (-x))^2-Q (R.referenceSpeed.q (-x)) at ht
  rw [R.coordinate_reflection,Q_reflection] at ht
  exact contact_bracket_negative hσ hq hξ hf.1 hr.1 hf.2 hh (by linarith) (by linarith)
    (R.filter_order_coordinate hσ hx).1 (R.filter_order_coordinate hσ hx).2

/--
The stated quantitative bound `R.contactDerivative hσ q x < 0`.

Use: `chebyshev2.Calibration.ReferenceData.contactFunctional_strictAnti_left` uses this
bound to establish `StrictAntiOn (R.contactFunctional hσ q) (Icc
(R.referenceSpeed.X 0) (R.referenceSpeed.X q))`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates `chebyshev2.PrescribedSpeed.SpeedData.X_strictMono`,
`chebyshev2.PrescribedSpeed.SpeedData.q_X`,
`chebyshev2.Calibration.ReferenceData.coordinate_strictMono` with the arguments shown in
the proof.
-/
theorem contactDerivative_negative {q x : ℝ} (hq : q ∈ Ioc (0:ℝ) 1)
    (hx : R.referenceSpeed.X 0 < x) (hxq : x < R.referenceSpeed.X q) :
    R.contactDerivative hσ q x < 0 := by
  -- Use the identities/estimates `chebyshev2.PrescribedSpeed.SpeedData.X_strictMono`,
  -- `chebyshev2.PrescribedSpeed.SpeedData.q_X`,
  -- `chebyshev2.Calibration.ReferenceData.coordinate_strictMono` with the arguments shown
  -- in the proof.
  have hq2 : q ∈ Icc (0:ℝ) 2 := ⟨hq.1.le,by linarith [hq.2]⟩
  have hX : R.referenceSpeed.X q < R.referenceSpeed.X 2 :=
    R.referenceSpeed.X_strictMono hq2 (by norm_num) (by linarith [hq.2])
  have hi : x ∈ Ioo (R.referenceSpeed.X 0) (R.referenceSpeed.X 2) := ⟨hx,hxq.trans hX⟩
  have hξ : R.referenceSpeed.q x < q := by
    simpa only [R.referenceSpeed.q_X hq2] using
      R.coordinate_strictMono ⟨hx.le,hi.2.le⟩
        ⟨(R.referenceSpeed.X_strictMono.monotoneOn (by norm_num) hq2 hq.1.le),hX.le⟩ hxq
  have hh : R.contact hσ x ≤ q := by
    change R.referenceSpeed.q x-R.filter hσ x ≤ q
    linarith [(R.filter_bounds hσ x).1]
  have hb := R.contact_bracket_negative_interior hσ hq hi hh
  have hn := add_nonneg (R.filter_bounds hσ x).1 (R.filter_bounds hσ (-x)).1
  exact mul_neg_of_pos_of_neg (div_pos (by linarith) (by positivity)) hb

/--
The stated quantitative bound `0 < R.contactDerivative hσ q x`.

Use: `chebyshev2.Calibration.ReferenceData.contactFunctional_strictMono_right` uses this
bound to establish `StrictMonoOn (R.contactFunctional hσ q) (Icc
(R.referenceSpeed.X q) (R.contactInverse hσ ⟨q,⟨hq.1.le,by linarith [hq.2]⟩⟩))`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.

Proof: Separate `x < R.referenceSpeed.X 2` from its negation; prove the goal under each of
these mutually exclusive hypotheses.
-/
theorem contactDerivative_positive {q x : ℝ} (hq : q ∈ Ioc (0:ℝ) 1)
    (hxq : R.referenceSpeed.X q < x) (hh : R.contact hσ x ≤ q) :
    0 < R.contactDerivative hσ q x := by
  -- Separate `x < R.referenceSpeed.X 2` from its negation; prove the goal under each of these
  -- mutually exclusive hypotheses.
  have hq2 : q ∈ Icc (0:ℝ) 2 := ⟨hq.1.le,by linarith [hq.2]⟩
  have ha : R.referenceSpeed.X 0 < R.referenceSpeed.X q :=
    R.referenceSpeed.X_strictMono (by norm_num) hq2 hq.1
  have hx := ha.trans hxq
  have hn := add_nonneg (R.filter_bounds hσ x).1 (R.filter_bounds hσ (-x)).1
  by_cases ht : x < R.referenceSpeed.X 2
  · have hi : x ∈ Ioo (R.referenceSpeed.X 0) (R.referenceSpeed.X 2) := ⟨hx,ht⟩
    have hξ : q < R.referenceSpeed.q x := by
      simpa only [R.referenceSpeed.q_X hq2] using
        R.coordinate_strictMono ⟨ha.le,hxq.le.trans ht.le⟩ ⟨hx.le,ht.le⟩ hxq
    have hb := R.contact_bracket_negative_interior hσ hq hi hh
    exact mul_pos_of_neg_of_neg (div_neg_of_neg_of_pos (by linarith) (by positivity)) hb
  · have hright := not_lt.mp ht
    have hX := R.X_reflection 0
    norm_num only [sub_zero] at hX
    have hleft : -x ≤ R.referenceSpeed.X 0 := by linarith
    have hf := R.filter_positive hσ hx
    dsimp only [contactDerivative,contactXi]
    rw [R.referenceSpeed.q_two_right hright,R.filter_zero_left hσ hleft]
    norm_num only [Q,sub_self,mul_zero,zero_mul,add_zero,sub_zero]
    have h1 : 2*(q-2)/(2+σ*R.filter hσ x) < 0 := div_neg_of_neg_of_pos
      (by linarith [hq.2]) (by positivity)
    have h2 : (1+σ)*R.filter hσ x*(q-2) < 0 := mul_neg_of_pos_of_neg
      (mul_pos (by linarith) hf) (by linarith [hq.2])
    exact mul_pos_of_neg_of_neg h1 h2

end
end chebyshev2.Calibration.ReferenceData
