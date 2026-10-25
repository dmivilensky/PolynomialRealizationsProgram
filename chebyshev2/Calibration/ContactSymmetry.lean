import chebyshev2.Calibration.ContactFlow

/-!
Article: chebyshev2, Theorem 3.2.
The reflection involution of the contact potential and monotonicity of h+g(h), including the linear
tail.
Use: `chebyshev2.Calibration.ReferenceData.calibration_F_reflection` feeds
`chebyshev2.Calibration.ReferenceData.calibration_physical_strict_minimum_upper` (calibration
physical strict minimum upper).
Proof chain: `chebyshev2.Calibration.ReferenceData.calibration_Gamma` — chebyshev2, Theorem
3.2; Constructed contact potential and calibrated reference.
-/
namespace chebyshev2.Calibration.ReferenceData
noncomputable section
open Set Real
set_option backward.isDefEq.respectTransparency false
variable (R : ReferenceData) {σ : ℝ} (hσ : 0 < σ)

/--
Exact identity `R.contact hσ x=0`.

Use: `chebyshev2.Calibration.ReferenceData.calibration_Gamma_contact` rewrites with this
identity to establish `(R.calibration hσ hb hω).Gamma
(R.referenceSpeed.q x)= (R.calibration hσ hb hω).F (R.referenceSpeed.q x) (R.contact hσ x)`.

Article: chebyshev2, Proposition 5 via
`chebyshev2.Calibration.ReferenceData.selfConsistent_attainment`.

Proof: Use the identities/estimates `chebyshev2.PrescribedSpeed.SpeedData.q_zero_left`,
`chebyshev2.Calibration.ReferenceData.filter_zero_left` with the arguments shown in the
proof.
-/
theorem contact_zero_left {x : ℝ} (hx : x ≤ R.referenceSpeed.X 0) : R.contact hσ x=0 := by rw [contact,R.referenceSpeed.q_zero_left hx,R.filter_zero_left hσ hx,sub_zero]

/--
The stated quantitative bound `0 ≤ R.contactSlope hσ x`.

Use: `chebyshev2.Calibration.ReferenceData.contact_monotone` uses this bound to establish
monotonicity in increasing order: `Monotone (R.contact hσ)`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.

Proof: Separate `R.referenceSpeed.X 0 < x` from its negation; prove the goal under each of
these mutually exclusive hypotheses.
-/
theorem contactSlope_nonneg (x : ℝ) : 0 ≤ R.contactSlope hσ x := by
  by_cases hx : R.referenceSpeed.X 0 < x
  · exact (R.contactSlope_positive hσ hx).le
  · dsimp only [contactSlope]
    rw [R.referenceSpeed.q_zero_left (not_lt.mp hx),R.filter_zero_left hσ (not_lt.mp hx)]
    norm_num [Q]

/--
Monotonicity in increasing order: `Monotone (R.contact hσ)`.

Use: `chebyshev2.Calibration.ReferenceData.potential_plus_id_monotone` uses this assertion
to establish monotonicity in increasing order: `MonotoneOn (fun h => h+R.potential hσ h) (Icc
(0:ℝ) 2)`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates
`chebyshev2.Calibration.ReferenceData.contact_derivative`,
`chebyshev2.Calibration.ReferenceData.contactSlope_nonneg` with the arguments shown in the
proof.
-/
theorem contact_monotone : Monotone (R.contact hσ) := by
  apply monotone_of_deriv_nonneg (fun x => (R.contact_derivative hσ x).differentiableAt)
  intro x
  rw [(R.contact_derivative hσ x).deriv]
  exact R.contactSlope_nonneg hσ x

/--
Defines `involution` of type `ℝ` by `2-h-R.potential hσ h`.

Use: `chebyshev2.Calibration.ReferenceData.involution_contact` rewrites with this
definition to establish the identity `R.involution hσ (R.contact hσ x)=R.contact hσ (-x)`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.
-/
def involution (h : ℝ) : ℝ := 2-h-R.potential hσ h

/--
Exact identity `R.involution hσ (R.contact hσ x)=R.contact hσ (-x)`.

Use: `chebyshev2.Calibration.ReferenceData.potential_plus_id_monotone` uses this identity
to establish monotonicity in increasing order: `MonotoneOn (fun h => h+R.potential hσ h) (Icc
(0:ℝ) 2)`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates
`chebyshev2.Calibration.ReferenceData.potential_contact`,
`chebyshev2.Calibration.ReferenceData.coordinate_reflection` with the arguments shown in
the proof.
-/
theorem involution_contact {x : ℝ} (hx : R.referenceSpeed.X 0 ≤ x) :
    R.involution hσ (R.contact hσ x)=R.contact hσ (-x) := by
  rw [involution,R.potential_contact hσ hx]
  dsimp only [contact]
  rw [R.coordinate_reflection]
  ring

/--
Monotonicity in increasing order: `MonotoneOn (fun h => h+R.potential hσ h) (Icc (0:ℝ) 2)`.

Use: `chebyshev2.Calibration.ReferenceData.calibration_beyond_diagonal` uses this identity
to prove the bound `(R.calibration hσ hb hω).F q q ≤ (R.calibration hσ
hb hω).F q h`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.

Proof: Separate `t=2` from its negation; prove the goal under each of these mutually exclusive
hypotheses. Assume the failure of the desired conclusion and derive a contradiction from the
available bounds/identities.
-/
theorem potential_plus_id_monotone : MonotoneOn (fun h => h+R.potential hσ h) (Icc (0:ℝ) 2) := by
  -- Separate `t=2` from its negation; prove the goal under each of these mutually exclusive
  -- hypotheses.
  intro h hh t ht hht
  change h+R.potential hσ h ≤ t+R.potential hσ t
  by_cases he : t=2
  · subst t
    rw [R.potential_two hσ]
    linarith [(R.potential_bounds hσ hh).2]
  · have ht' : t ∈ Ico (0:ℝ) 2 := ⟨ht.1,lt_of_le_of_ne ht.2 he⟩
    have hh' : h ∈ Ico (0:ℝ) 2 := ⟨hh.1,hht.trans_lt ht'.2⟩
    let x := R.contactInverse hσ ⟨h,hh'⟩
    let y := R.contactInverse hσ ⟨t,ht'⟩
    have hx := R.contactInverse_mem hσ ⟨h,hh'⟩
    have hy := R.contactInverse_mem hσ ⟨t,ht'⟩
    have hc : R.contact hσ x=h := R.contact_inverse hσ _
    have hd : R.contact hσ y=t := R.contact_inverse hσ _
    have hxy : x ≤ y := by
      by_contra hn
      have hm := R.contact_strictMono hσ hy hx (not_le.mp hn)
      rw [hc,hd] at hm
      linarith
    have hm := R.contact_monotone hσ (neg_le_neg hxy)
    have hi := R.involution_contact hσ hx
    have hj := R.involution_contact hσ hy
    rw [hc] at hi
    rw [hd] at hj
    rw [← hi,← hj] at hm
    dsimp only [involution] at hm
    linarith

/--
The stated quantitative bound `Q h ≤ 2*R.potential hσ h+σ*(R.potential hσ h)^2`.

Use: `chebyshev2.Calibration.ReferenceData.calibration_beyond_diagonal` uses this bound to
establish the stated quantitative bound `(R.calibration hσ hb hω).F q q ≤ (R.calibration hσ hb
hω).F q h`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.

Proof: Separate `h=2` from its negation; prove the goal under each of these mutually exclusive
hypotheses.
-/
theorem potential_quadratic_threshold {h : ℝ} (hh : h ∈ Icc (0:ℝ) 2) :
    Q h ≤ 2*R.potential hσ h+σ*(R.potential hσ h)^2 := by
  -- Separate `h=2` from its negation; prove the goal under each of these mutually exclusive
  -- hypotheses.
  by_cases he : h=2
  · subst h
    rw [R.potential_two hσ]
    norm_num [Q]
  · have hh' : h ∈ Ico (0:ℝ) 2 := ⟨hh.1,lt_of_le_of_ne hh.2 he⟩
    let x := R.contactInverse hσ ⟨h,hh'⟩
    have hx := R.contactInverse_mem hσ ⟨h,hh'⟩
    have hc : R.contact hσ x=h := R.contact_inverse hσ _
    have hg : R.potential hσ h=R.filter hσ x+R.filter hσ (-x) := by
      rw [← hc]
      exact R.potential_contact hσ hx
    have hs := R.contactSlope_nonneg hσ (-x)
    change 0 ≤ 2*R.filter hσ (-x)+σ*(R.filter hσ (-x))^2-Q (R.referenceSpeed.q (-x)) at hs
    rw [R.coordinate_reflection,Q_reflection] at hs
    have hf := (R.filter_bounds hσ x).1
    have hr := (R.filter_bounds hσ (-x)).1
    have hq := (R.referenceSpeed.q_mem x).2
    have h1 := mul_nonneg (show 0 ≤ 2*(2-R.referenceSpeed.q x) by linarith) hf
    have h2 := mul_nonneg (show 0 ≤ 1+σ by linarith) (sq_nonneg (R.filter hσ x))
    have h3 := mul_nonneg (mul_nonneg (show 0 ≤ 2*σ by positivity) hf) hr
    change R.referenceSpeed.q x-R.filter hσ x=h at hc
    rw [hg,← hc]
    unfold Q at *
    nlinarith

/--
Membership in the specified domain/enclosure: `R.contact hσ (-x) ∈ Icc (0:ℝ) 2`.

Use: `chebyshev2.Calibration.ReferenceData.calibration_physical_strict_minimum_upper` uses
this assertion to prove the bound `(R.calibration hσ hb hω).F q
(R.contact hσ (R.referenceSpeed.X q)) < (R.calibration hσ hb hω).F q (R.contact hσ x)`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates `chebyshev2.Calibration.ReferenceData.X_reflection`,
`chebyshev2.Calibration.ReferenceData.contact_nonneg`,
`chebyshev2.Calibration.ReferenceData.contact_lt_two` with the arguments shown in the
proof.
-/
theorem involution_contact_mem {x : ℝ}
    (hx : x ∈ Icc (R.referenceSpeed.X 0) (R.referenceSpeed.X 2)) :
    R.contact hσ (-x) ∈ Icc (0:ℝ) 2 := by
  have hX := R.X_reflection 0
  norm_num only [sub_zero] at hX
  have hl : R.referenceSpeed.X 0 ≤ -x := by linarith [hx.2]
  exact ⟨R.contact_nonneg hσ hl,(R.contact_lt_two hσ hl).le⟩

/--
Exact identity `R.potential hσ (R.contact hσ (-x))=R.potential hσ (R.contact hσ x)`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Theorem 3.2.

Proof: Use the identities/estimates `chebyshev2.Calibration.ReferenceData.X_reflection`,
`chebyshev2.Calibration.ReferenceData.potential_contact` with the arguments shown in the
proof.
-/
theorem potential_contact_reflection {x : ℝ}
    (hx : x ∈ Icc (R.referenceSpeed.X 0) (R.referenceSpeed.X 2)) :
    R.potential hσ (R.contact hσ (-x))=R.potential hσ (R.contact hσ x) := by
  have hX := R.X_reflection 0
  norm_num only [sub_zero] at hX
  rw [R.potential_contact hσ hx.1,R.potential_contact hσ (by linarith [hx.2]),neg_neg,add_comm]

/--
The precise assertion is `(R.calibration hσ hb hω).F q (R.contact hσ x)= (R.calibration hσ hb
hω).F (2-q) (R.contact hσ (-x))`.

Use: `chebyshev2.Calibration.ReferenceData.calibration_physical_strict_minimum_upper`
rewrites with this identity to prove the bound `(R.calibration hσ hb
hω).F q (R.contact hσ (R.referenceSpeed.X q)) < (R.calibration hσ hb hω).F q (R.contact hσ x)`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates
`chebyshev2.Calibration.ReferenceData.calibration_contactFunctional`,
`chebyshev2.Calibration.ReferenceData.X_reflection`,
`chebyshev2.Calibration.ReferenceData.coordinate_reflection` with the arguments shown in
the proof.
-/
theorem calibration_F_reflection {b ω q x : ℝ} (hb : 0 < b) (hω : 0 ≤ ω)
    (hx : x ∈ Icc (R.referenceSpeed.X 0) (R.referenceSpeed.X 2)) :
    (R.calibration hσ hb hω).F q (R.contact hσ x)=
      (R.calibration hσ hb hω).F (2-q) (R.contact hσ (-x)) := by
  -- Use the identities/estimates
  -- `chebyshev2.Calibration.ReferenceData.calibration_contactFunctional`,
  -- `chebyshev2.Calibration.ReferenceData.X_reflection`,
  -- `chebyshev2.Calibration.ReferenceData.coordinate_reflection` with the arguments shown
  -- in the proof.
  rw [R.calibration_contactFunctional hσ hb hω q hx.1]
  have hX := R.X_reflection 0
  norm_num only [sub_zero] at hX
  rw [R.calibration_contactFunctional hσ hb hω (2-q) (by linarith [hx.2])]
  dsimp only [contactFunctional,contact]
  rw [R.coordinate_reflection,neg_neg]
  congr 1
  · ring
  · ring

end
end chebyshev2.Calibration.ReferenceData
