import chebyshev2.Calibration.GlobalMinimum
import chebyshev2.Calibration.Filter

/-!
Article: chebyshev2, Theorem 3.2.
Lemma 9: the contact part and the logarithmic tail of the actual J.
Use: `chebyshev2.Calibration.ReferenceData.calibration_constant` feeds
`chebyshev2.Calibration.ReferenceData.calibration_constant_normalized` (calibration constant
normalized).
Proof chain: `chebyshev2.Calibration.ReferenceData.calibration_constant_normalized` —
chebyshev2, Theorem 3.2; Constructed contact potential and calibrated reference.
-/
namespace chebyshev2.Calibration.ReferenceData
noncomputable section
open Set MeasureTheory Real
set_option backward.isDefEq.respectTransparency false
variable (R : ReferenceData) {σ : ℝ} (hσ : 0 < σ)

/--
The precise assertion is `(R.calibration hσ hb hω).Gamma q= (R.calibration hσ hb hω).F q
(R.contact hσ (R.referenceSpeed.X q))`.

Use: `chebyshev2.Calibration.ReferenceData.calibration_Gamma_on_support` uses this identity
to establish `(R.calibration hσ hb hω).Gamma (R.referenceSpeed.q x)=
(R.calibration hσ hb hω).F (R.referenceSpeed.q x) (R.contact hσ x)`.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Separate `q ∈ Ioo (0:ℝ) 2` from its negation; prove the goal under each of these
mutually exclusive hypotheses.
-/
theorem calibration_Gamma_at_X {b ω q : ℝ} (hb : 0 < b) (hω : 0 ≤ ω)
    (hq : q ∈ Icc (0:ℝ) 2) :
    (R.calibration hσ hb hω).Gamma q=
      (R.calibration hσ hb hω).F q (R.contact hσ (R.referenceSpeed.X q)) := by
  -- Separate `q ∈ Ioo (0:ℝ) 2` from its negation; prove the goal under each of these mutually
  -- exclusive hypotheses.
  by_cases hi : q ∈ Ioo (0:ℝ) 2
  · exact R.calibration_Gamma hσ hb hω hi
  · rcases Data.endpoint_cases hq hi with he | he
    · subst q
      rw [R.contact_left hσ,Data.Gamma_zero]
      simp [Data.F]
    · subst q
      let C := R.calibration hσ hb hω
      have hh : R.contact hσ (R.referenceSpeed.X 2) ∈ Icc (0:ℝ) 2 :=
        ⟨R.contact_nonneg hσ R.referenceSpeed.X_endpoint_order.le,
          (R.contact_lt_two hσ R.referenceSpeed.X_endpoint_order.le).le⟩
      have hg : C.potential (R.contact hσ (R.referenceSpeed.X 2))=2-R.contact hσ (R.referenceSpeed.X 2) := by
        rw [C.potential_eq hh]
        exact R.potential_tail hσ hh le_rfl
      rw [C.F_tail_value hg,C.Gamma_two]
      norm_num

/--
The precise assertion is `(R.calibration hσ hb hω).Gamma (R.referenceSpeed.q x)= (R.calibration
hσ hb hω).F (R.referenceSpeed.q x) (R.contact hσ x)`.

Use: `chebyshev2.Calibration.ReferenceData.J_contact_derivative` rewrites with this
identity to establish the actual derivative at the stated point: `HasDerivAt (fun x =>
(R.calibration hσ hb hω).J (R.contact hσ x)) ((R.calibration hσ hb hω).Gamma
(R.referenceSpeed.q x)-(R.filter hσ x)^2) x`.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Use the identities/estimates
`chebyshev2.Calibration.ReferenceData.calibration_Gamma_at_X`,
`chebyshev2.PrescribedSpeed.SpeedData.q_mem`,
`chebyshev2.PrescribedSpeed.SpeedData.X_q` with the arguments shown in the proof.
-/
theorem calibration_Gamma_on_support {b ω x : ℝ} (hb : 0 < b) (hω : 0 ≤ ω)
    (hx : x ∈ Icc (R.referenceSpeed.X 0) (R.referenceSpeed.X 2)) :
    (R.calibration hσ hb hω).Gamma (R.referenceSpeed.q x)=
      (R.calibration hσ hb hω).F (R.referenceSpeed.q x) (R.contact hσ x) := by
  have h := R.calibration_Gamma_at_X hσ hb hω (R.referenceSpeed.q_mem x)
  rwa [R.referenceSpeed.X_q hx] at h

/--
The actual derivative at the stated point: `HasDerivAt (fun x => (R.calibration hσ hb hω).J
(R.contact hσ x)) ((R.calibration hσ hb hω).Gamma (R.referenceSpeed.q x)-(R.filter hσ x)^2) x`.

Use: `chebyshev2.Calibration.ReferenceData.J_contact_integral` uses this derivative formula
to establish the identity stated in that declaration.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Use the identities/estimates `chebyshev2.Calibration.Data.J_derivative`,
`chebyshev2.Calibration.ReferenceData.contact_derivative`,
`chebyshev2.Calibration.Data.calibration_identity` with the arguments shown in the proof.
-/
theorem J_contact_derivative {b ω x : ℝ} (hb : 0 < b) (hω : 0 ≤ ω)
    (hx : x ∈ Icc (R.referenceSpeed.X 0) (R.referenceSpeed.X 2)) :
    HasDerivAt (fun x => (R.calibration hσ hb hω).J (R.contact hσ x))
      ((R.calibration hσ hb hω).Gamma (R.referenceSpeed.q x)-(R.filter hσ x)^2) x := by
  -- Use the identities/estimates `chebyshev2.Calibration.Data.J_derivative`,
  -- `chebyshev2.Calibration.ReferenceData.contact_derivative`,
  -- `chebyshev2.Calibration.Data.calibration_identity` with the arguments shown in the
  -- proof.
  let C := R.calibration hσ hb hω
  have h := (C.J_derivative (R.contact hσ x)).comp x (R.contact_derivative hσ x)
  have halg := C.calibration_identity (R.referenceSpeed.q x) (R.contact hσ x)
  change (R.referenceSpeed.q x-(R.referenceSpeed.q x-R.filter hσ x))^2+
    C.Jprime (R.contact hσ x)*((R.referenceSpeed.q x)^2+σ*(R.referenceSpeed.q x-
      (R.referenceSpeed.q x-R.filter hσ x))^2-2*R.contact hσ x)=C.F (R.referenceSpeed.q x) (R.contact hσ x) at halg
  rw [← R.calibration_Gamma_on_support hσ hb hω hx] at halg
  convert! h using 1
  dsimp only [contactSlope,contact] at *
  unfold Q at *
  nlinarith [halg]

/--
The precise assertion is `(R.calibration hσ hb hω).J (R.contact hσ (R.referenceSpeed.X 2))= ∫ x
in (R.referenceSpeed.X 0)..(R.referenceSpeed.X 2), (R.calibration hσ hb hω).Gamma
(R.referenceSpeed.q x)-(R.filter hσ x)^2`.

Use: `chebyshev2.Calibration.ReferenceData.J_contact_half_integral` rewrites with this
identity to establish the identity stated in that declaration.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Use the identities/estimates `chebyshev2.Calibration.Data.Gamma_continuous`,
`chebyshev2.PrescribedSpeed.SpeedData.q_continuous`,
`chebyshev2.Calibration.ReferenceData.filter_c1` with the arguments shown in the proof.
-/
theorem J_contact_integral {b ω : ℝ} (hb : 0 < b) (hω : 0 ≤ ω) :
    (R.calibration hσ hb hω).J (R.contact hσ (R.referenceSpeed.X 2))=
      ∫ x in (R.referenceSpeed.X 0)..(R.referenceSpeed.X 2),
        (R.calibration hσ hb hω).Gamma (R.referenceSpeed.q x)-(R.filter hσ x)^2 := by
  -- Use the identities/estimates `chebyshev2.Calibration.Data.Gamma_continuous`,
  -- `chebyshev2.PrescribedSpeed.SpeedData.q_continuous`,
  -- `chebyshev2.Calibration.ReferenceData.filter_c1` with the arguments shown in the
  -- proof.
  let C := R.calibration hσ hb hω
  -- Establish continuity hc before using the function at limits or in calculus arguments.
  have hc : Continuous (fun x => C.Gamma (R.referenceSpeed.q x)-(R.filter hσ x)^2) :=
    (C.Gamma_continuous.comp R.referenceSpeed.q_continuous).sub ((R.filter_c1 hσ).continuous.pow 2)
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x hx => R.J_contact_derivative hσ hb hω (by simpa only [uIcc_of_le R.referenceSpeed.X_endpoint_order.le] using hx))
    (hc.intervalIntegrable (R.referenceSpeed.X 0) (R.referenceSpeed.X 2))
  rw [R.contact_left hσ,C.J_zero,sub_zero] at hi
  exact hi.symm

/--
The precise assertion is `(R.calibration hσ hb hω).J 2- (R.calibration hσ hb hω).J (R.contact
hσ (R.referenceSpeed.X 2))= -(σ*R.filter hσ (R.referenceSpeed.X 2)- 2*log (1+σ*R.filter hσ
(R.referenceSpeed.X 2)/2))/σ^2`.

Use: `chebyshev2.Calibration.ReferenceData.calibration_constant` uses this identity to
establish the identity stated in that declaration.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem J_tail {b ω : ℝ} (hb : 0 < b) (hω : 0 ≤ ω) :
    (R.calibration hσ hb hω).J 2-
      (R.calibration hσ hb hω).J (R.contact hσ (R.referenceSpeed.X 2))=
    -(σ*R.filter hσ (R.referenceSpeed.X 2)-
      2*log (1+σ*R.filter hσ (R.referenceSpeed.X 2)/2))/σ^2 := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  let C := R.calibration hσ hb hω
  let a := R.contact hσ (R.referenceSpeed.X 2)
  let P := fun h : ℝ => (2-h)/σ-2/σ^2*log (1+σ*(2-h)/2)
  have ha : a ∈ Icc (0:ℝ) 2 :=
    ⟨R.contact_nonneg hσ R.referenceSpeed.X_endpoint_order.le,
      (R.contact_lt_two hσ R.referenceSpeed.X_endpoint_order.le).le⟩
  have hP : ∀ h ∈ uIcc a 2, HasDerivAt P (C.Jprime h) h := by
    intro h hh
    rw [uIcc_of_le ha.2] at hh
    have hh2 : h ∈ Icc (0:ℝ) 2 := ⟨ha.1.trans hh.1,hh.2⟩
    have hg : C.potential h=2-h := by
      rw [C.potential_eq hh2]
      exact R.potential_tail hσ hh2 hh.1
    have hden : 1+σ*(2-h)/2 ≠ 0 := ne_of_gt (by
      have hp := mul_nonneg hσ.le (sub_nonneg.mpr hh.2)
      nlinarith)
    have hw : HasDerivAt (fun h : ℝ => 2-h) (-1) h := by
      convert! (hasDerivAt_id h).const_sub 2 using 1
    have hp := (hw.div_const σ).sub
      (((hw.const_mul σ |>.div_const 2 |>.const_add 1).log hden).const_mul (2/σ^2))
    convert! hp using 1
    rw [Data.Jprime,hg]
    change -(2-h)/(2+σ*(2-h))= -1/σ-2/σ^2*(σ*(-1)/2/(1+σ*(2-h)/2))
    have hz : 2+σ*(2-h) ≠ 0 := ne_of_gt (by
      have hn := mul_nonneg hσ.le (sub_nonneg.mpr hh2.2)
      linarith)
    field_simp (disch := solve | norm_num | assumption | exact hσ.ne' |
      (convert hz using 1; ring))
    ring
  have h1 := intervalIntegral.integral_eq_sub_of_hasDerivAt hP (C.Jprime_continuous.intervalIntegrable a 2)
  have h2 := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun h (_ : h ∈ uIcc a 2) => C.J_derivative h) (C.Jprime_continuous.intervalIntegrable a 2)
  have hc : 2-a=R.filter hσ (R.referenceSpeed.X 2) := by
    change 2-(R.referenceSpeed.q (R.referenceSpeed.X 2)-R.filter hσ (R.referenceSpeed.X 2))=_
    rw [R.referenceSpeed.q_X (by norm_num)]
    ring
  rw [h2] at h1
  dsimp only [P] at h1
  rw [hc] at h1
  norm_num only [sub_self,mul_zero,zero_div,add_zero,log_one,sub_zero,zero_mul] at h1
  rw [h1]
  field_simp
  ring

/--
The precise assertion is `(R.calibration hσ hb hω).J (R.contact hσ (R.referenceSpeed.X 2))= ∫ x
in (R.referenceSpeed.X 0)..0, 2*(R.calibration hσ hb hω).Gamma (R.referenceSpeed.q x)-
(R.filter hσ x)^2-(R.filter hσ (-x))^2`.

Use: `chebyshev2.Calibration.ReferenceData.calibration_constant` rewrites with this
identity to establish the identity stated in that declaration.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Use the identities/estimates `chebyshev2.Calibration.Data.Gamma_continuous`,
`chebyshev2.PrescribedSpeed.SpeedData.q_continuous`,
`chebyshev2.Calibration.ReferenceData.filter_c1` with the arguments shown in the proof.
-/
theorem J_contact_half_integral {b ω : ℝ} (hb : 0 < b) (hω : 0 ≤ ω) :
    (R.calibration hσ hb hω).J (R.contact hσ (R.referenceSpeed.X 2))=
      ∫ x in (R.referenceSpeed.X 0)..0,
        2*(R.calibration hσ hb hω).Gamma (R.referenceSpeed.q x)-
          (R.filter hσ x)^2-(R.filter hσ (-x))^2 := by
  -- Use the identities/estimates `chebyshev2.Calibration.Data.Gamma_continuous`,
  -- `chebyshev2.PrescribedSpeed.SpeedData.q_continuous`,
  -- `chebyshev2.Calibration.ReferenceData.filter_c1` with the arguments shown in the
  -- proof.
  let C := R.calibration hσ hb hω
  let f := fun x => C.Gamma (R.referenceSpeed.q x)-(R.filter hσ x)^2
  -- Establish continuity hf before using the function at limits or in calculus arguments.
  have hf : Continuous f := (C.Gamma_continuous.comp R.referenceSpeed.q_continuous).sub
    ((R.filter_c1 hσ).continuous.pow 2)
  have hX := R.X_reflection 0
  norm_num only [sub_zero] at hX
  have he := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hf.intervalIntegrable (R.referenceSpeed.X 0) 0)
    (hf.intervalIntegrable 0 (R.referenceSpeed.X 2))
  have hr : (∫ x in (0:ℝ)..(R.referenceSpeed.X 2), f x)=
      ∫ x in (R.referenceSpeed.X 0)..0, f (-x) := by
    rw [intervalIntegral.integral_comp_neg,neg_zero,← hX]
  rw [R.J_contact_integral hσ hb hω,← he,hr,
    ← intervalIntegral.integral_add (hf.intervalIntegrable _ _)
      (show IntervalIntegrable (fun x : ℝ => f (-x)) volume (R.referenceSpeed.X 0) 0 from (hf.comp continuous_neg).intervalIntegrable _ _)]
  apply intervalIntegral.integral_congr
  intro x hx
  rw [uIcc_of_le R.X_zero_negative.le] at hx
  dsimp only [f]
  rw [R.coordinate_reflection,R.calibration_Gamma_reflection hσ hb hω _ (R.referenceSpeed.q_mem x)]
  ring

/--
Lemma 9 in centered coordinates; translating by -X(0) gives the printed integral from zero to
the midpoint of the support.

Use: `chebyshev2.Calibration.ReferenceData.calibration_constant_normalized` rewrites with
this identity to establish `(R.calibration hσ hb ho).J 2= (∫ t in Icc
(0:ℝ) 1,R.contactCoreIntegrand hσ t)- vacuumSquare σ (R.normalizedReflectedFilter hσ 0)`.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Use the identities/estimates `chebyshev2.Calibration.ReferenceData.J_tail`,
`chebyshev2.Calibration.ReferenceData.J_contact_half_integral` with the arguments shown in
the proof.
-/
theorem calibration_constant {b ω : ℝ} (hb : 0 < b) (hω : 0 ≤ ω) :
    (R.calibration hσ hb hω).J 2=
      (∫ x in (R.referenceSpeed.X 0)..0,
        2*(R.calibration hσ hb hω).Gamma (R.referenceSpeed.q x)-
          (R.filter hσ x)^2-(R.filter hσ (-x))^2)-
      (σ*R.filter hσ (R.referenceSpeed.X 2)-
        2*log (1+σ*R.filter hσ (R.referenceSpeed.X 2)/2))/σ^2 := by
  -- Use the identities/estimates `chebyshev2.Calibration.ReferenceData.J_tail`,
  -- `chebyshev2.Calibration.ReferenceData.J_contact_half_integral` with the arguments
  -- shown in the proof.
  have ht := R.J_tail hσ hb hω
  rw [R.J_contact_half_integral hσ hb hω,neg_div] at ht
  linarith

end
end chebyshev2.Calibration.ReferenceData
