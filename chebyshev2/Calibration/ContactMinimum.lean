import chebyshev2.Calibration.ContactSigns

/-!
Article: chebyshev2, Theorem 3.2.
The unique contact minimum on the defining interval of Gamma, for the lower half 0 < q <= 1.
Use: `chebyshev2.Calibration.ReferenceData.calibration_strict_minimum_lower` feeds
`chebyshev2.Calibration.ReferenceData.calibration_Gamma_lower` (calibration Gamma lower).
Proof chain: `chebyshev2.Calibration.ReferenceData.calibration_Gamma` — chebyshev2, Theorem
3.2; Constructed contact potential and calibrated reference.
-/
namespace chebyshev2.Calibration.ReferenceData
noncomputable section
open Set Real
set_option backward.isDefEq.respectTransparency false
variable (R : ReferenceData) {σ : ℝ} (hσ : 0 < σ)

/--
The precise assertion is `StrictAntiOn (R.contactFunctional hσ q) (Icc (R.referenceSpeed.X 0)
(R.referenceSpeed.X q))`.

Use: `chebyshev2.Calibration.ReferenceData.contactFunctional_strict_minimum` uses this
assertion to prove the bound `R.contactFunctional hσ q
(R.referenceSpeed.X q) < R.contactFunctional hσ q (R.contactInverse hσ ⟨h,⟨hh.1,by linarith
[hh.2,hq.2]⟩⟩)`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates
`chebyshev2.Calibration.ReferenceData.contactFunctional_continuous`,
`chebyshev2.Calibration.ReferenceData.contactFunctional_derivative`,
`chebyshev2.Calibration.ReferenceData.contactDerivative_negative` with the arguments shown
in the proof.
-/
theorem contactFunctional_strictAnti_left {q : ℝ} (hq : q ∈ Ioc (0:ℝ) 1) :
    StrictAntiOn (R.contactFunctional hσ q)
      (Icc (R.referenceSpeed.X 0) (R.referenceSpeed.X q)) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _) (R.contactFunctional_continuous hσ q).continuousOn
  intro x hx
  rw [interior_Icc] at hx
  rw [(R.contactFunctional_derivative hσ q x).deriv]
  exact R.contactDerivative_negative hσ hq hx.1 hx.2

/--
The precise assertion is `StrictMonoOn (R.contactFunctional hσ q) (Icc (R.referenceSpeed.X q)
(R.contactInverse hσ ⟨q,⟨hq.1.le,by linarith [hq.2]⟩⟩))`.

Use: `chebyshev2.Calibration.ReferenceData.contactFunctional_strict_minimum` uses this
assertion to prove the bound `R.contactFunctional hσ q
(R.referenceSpeed.X q) < R.contactFunctional hσ q (R.contactInverse hσ ⟨h,⟨hh.1,by linarith
[hh.2,hq.2]⟩⟩)`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates
`chebyshev2.Calibration.ReferenceData.contactFunctional_continuous`,
`chebyshev2.Calibration.ReferenceData.contactFunctional_derivative`,
`chebyshev2.Calibration.ReferenceData.contactDerivative_positive` with the arguments shown
in the proof.
-/
theorem contactFunctional_strictMono_right {q : ℝ} (hq : q ∈ Ioc (0:ℝ) 1) :
    StrictMonoOn (R.contactFunctional hσ q)
      (Icc (R.referenceSpeed.X q) (R.contactInverse hσ ⟨q,⟨hq.1.le,by linarith [hq.2]⟩⟩)) := by
  -- Use the identities/estimates
  -- `chebyshev2.Calibration.ReferenceData.contactFunctional_continuous`,
  -- `chebyshev2.Calibration.ReferenceData.contactFunctional_derivative`,
  -- `chebyshev2.Calibration.ReferenceData.contactDerivative_positive` with the arguments
  -- shown in the proof.
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _) (R.contactFunctional_continuous hσ q).continuousOn
  intro x hx
  rw [interior_Icc] at hx
  rw [(R.contactFunctional_derivative hσ q x).deriv]
  apply R.contactDerivative_positive hσ hq hx.1
  have hq2 : q ∈ Icc (0:ℝ) 2 := ⟨hq.1.le,by linarith [hq.2]⟩
  have ha : R.referenceSpeed.X 0 < R.referenceSpeed.X q :=
    R.referenceSpeed.X_strictMono (by norm_num) hq2 hq.1
  have hm := (R.contact_strictMono hσ).monotoneOn (ha.le.trans hx.1.le)
    (R.contactInverse_mem hσ _) hx.2.le
  simpa only [R.contact_inverse hσ] using hm

/--
Membership in the specified domain/enclosure: `R.contact hσ (R.referenceSpeed.X q) ∈ Icc (0:ℝ)
q`.

Use: `chebyshev2.Calibration.ReferenceData.calibration_Gamma_lower` uses this assertion to
establish the precise assertion is `(R.calibration hσ hb hω).Gamma q= (R.calibration hσ hb
hω).F q (R.contact hσ (R.referenceSpeed.X q))`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates `chebyshev2.PrescribedSpeed.SpeedData.X_strictMono`,
`chebyshev2.Calibration.ReferenceData.contact_nonneg`,
`chebyshev2.PrescribedSpeed.SpeedData.q_X` with the arguments shown in the proof.
-/
theorem contact_at_X_bounds {q : ℝ} (hq : q ∈ Icc (0:ℝ) 2) :
    R.contact hσ (R.referenceSpeed.X q) ∈ Icc (0:ℝ) q := by
  have hx : R.referenceSpeed.X 0 ≤ R.referenceSpeed.X q :=
    R.referenceSpeed.X_strictMono.monotoneOn (by norm_num) hq hq.1
  refine ⟨R.contact_nonneg hσ hx,?_⟩
  change R.referenceSpeed.q (R.referenceSpeed.X q)-R.filter hσ (R.referenceSpeed.X q) ≤ q
  rw [R.referenceSpeed.q_X hq]
  linarith [(R.filter_bounds hσ (R.referenceSpeed.X q)).1]

/--
The stated quantitative bound `R.contactFunctional hσ q (R.referenceSpeed.X q) <
R.contactFunctional hσ q (R.contactInverse hσ ⟨h,⟨hh.1,by linarith [hh.2,hq.2]⟩⟩)`.

Use: `chebyshev2.Calibration.ReferenceData.calibration_strict_minimum_lower` uses this
bound to prove the bound `(R.calibration hσ hb hω).F q (R.contact hσ
(R.referenceSpeed.X q)) < (R.calibration hσ hb hω).F q h`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.

Proof: Assume the failure of the desired conclusion and derive a contradiction from the
available bounds/identities.
-/
theorem contactFunctional_strict_minimum {q h : ℝ} (hq : q ∈ Ioc (0:ℝ) 1)
    (hh : h ∈ Icc (0:ℝ) q) (hne : h ≠ R.contact hσ (R.referenceSpeed.X q)) :
    R.contactFunctional hσ q (R.referenceSpeed.X q) <
      R.contactFunctional hσ q (R.contactInverse hσ ⟨h,⟨hh.1,by linarith [hh.2,hq.2]⟩⟩) := by
  -- Assume the failure of the desired conclusion and derive a contradiction from the available
  -- bounds/identities.
  let x := R.contactInverse hσ ⟨h,⟨hh.1,by linarith [hh.2,hq.2]⟩⟩
  let y := R.contactInverse hσ ⟨q,⟨hq.1.le,by linarith [hq.2]⟩⟩
  have hq2 : q ∈ Icc (0:ℝ) 2 := ⟨hq.1.le,by linarith [hq.2]⟩
  have ha : R.referenceSpeed.X 0 ≤ R.referenceSpeed.X q :=
    R.referenceSpeed.X_strictMono.monotoneOn (by norm_num) hq2 hq.1.le
  have hx : R.referenceSpeed.X 0 ≤ x := R.contactInverse_mem hσ _
  have hy : R.referenceSpeed.X 0 ≤ y := R.contactInverse_mem hσ _
  have hc : R.contact hσ x=h := R.contact_inverse hσ _
  have hcy : R.contact hσ y=q := R.contact_inverse hσ _
  have hxy : x ≤ y := by
    by_contra hn
    have hm := R.contact_strictMono hσ hy hx (not_le.mp hn)
    rw [hc,hcy] at hm
    linarith [hh.2]
  have hqy : R.referenceSpeed.X q ≤ y := by
    by_contra hn
    have hm := R.contact_strictMono hσ hy ha (not_le.mp hn)
    rw [hcy] at hm
    linarith [(R.contact_at_X_bounds hσ hq2).2]
  have hnx : x ≠ R.referenceSpeed.X q := by
    intro he
    rw [he] at hc
    exact hne hc.symm
  rcases lt_or_gt_of_ne hnx with hl | hr
  · exact R.contactFunctional_strictAnti_left hσ hq ⟨hx,hl.le⟩ ⟨ha,le_rfl⟩ hl
  · exact R.contactFunctional_strictMono_right hσ hq ⟨le_rfl,hqy⟩ ⟨hr.le,hxy⟩ hr

/--
The stated quantitative bound `(R.calibration hσ hb hω).F q (R.contact hσ (R.referenceSpeed.X
q)) < (R.calibration hσ hb hω).F q h`.

Use: `chebyshev2.Calibration.ReferenceData.calibration_Gamma_lower` uses this bound to
establish the precise assertion is `(R.calibration hσ hb hω).Gamma q= (R.calibration hσ hb
hω).F q (R.contact hσ (R.referenceSpeed.X q))`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates `chebyshev2.PrescribedSpeed.SpeedData.X_strictMono`,
`chebyshev2.Calibration.ReferenceData.contact_inverse`,
`chebyshev2.Calibration.ReferenceData.calibration_contactFunctional` with the arguments
shown in the proof.
-/
theorem calibration_strict_minimum_lower {b ω q h : ℝ} (hb : 0 < b) (hω : 0 ≤ ω)
    (hq : q ∈ Ioc (0:ℝ) 1) (hh : h ∈ Icc (0:ℝ) q)
    (hne : h ≠ R.contact hσ (R.referenceSpeed.X q)) :
    (R.calibration hσ hb hω).F q (R.contact hσ (R.referenceSpeed.X q)) <
      (R.calibration hσ hb hω).F q h := by
  -- Use the identities/estimates `chebyshev2.PrescribedSpeed.SpeedData.X_strictMono`,
  -- `chebyshev2.Calibration.ReferenceData.contact_inverse`,
  -- `chebyshev2.Calibration.ReferenceData.calibration_contactFunctional` with the
  -- arguments shown in the proof.
  have hq2 : q ∈ Icc (0:ℝ) 2 := ⟨hq.1.le,by linarith [hq.2]⟩
  have ha : R.referenceSpeed.X 0 ≤ R.referenceSpeed.X q :=
    R.referenceSpeed.X_strictMono.monotoneOn (by norm_num) hq2 hq.1.le
  have hc := R.contact_inverse hσ ⟨h,⟨hh.1,by linarith [hh.2,hq.2]⟩⟩
  change R.contact hσ (R.contactInverse hσ ⟨h,⟨hh.1,by linarith [hh.2,hq.2]⟩⟩)=h at hc
  rw [← hc,R.calibration_contactFunctional hσ hb hω q ha,
    R.calibration_contactFunctional hσ hb hω q (R.contactInverse_mem hσ _)]
  exact R.contactFunctional_strict_minimum hσ hq hh hne

/--
The precise assertion is `(R.calibration hσ hb hω).Gamma q= (R.calibration hσ hb hω).F q
(R.contact hσ (R.referenceSpeed.X q))`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Theorem 3.2.

Proof: Separate `q*u=R.contact hσ (R.referenceSpeed.X q)` from its negation; prove the goal
under each of these mutually exclusive hypotheses.
-/
theorem calibration_Gamma_lower {b ω q : ℝ} (hb : 0 < b) (hω : 0 ≤ ω)
    (hq : q ∈ Ioc (0:ℝ) 1) :
    (R.calibration hσ hb hω).Gamma q=
      (R.calibration hσ hb hω).F q (R.contact hσ (R.referenceSpeed.X q)) := by
  -- Separate `q*u=R.contact hσ (R.referenceSpeed.X q)` from its negation; prove the goal under
  -- each of these mutually exclusive hypotheses.
  let C := R.calibration hσ hb hω
  have hh := R.contact_at_X_bounds hσ (show q ∈ Icc (0:ℝ) 2 from ⟨hq.1.le,by linarith [hq.2]⟩)
  apply le_antisymm (C.Gamma_le_state hq.1.le hh)
  obtain ⟨u,hu,he⟩ := C.Gamma_attained q
  rw [← he]
  by_cases hn : q*u=R.contact hσ (R.referenceSpeed.X q)
  · exact (congrArg (C.F q) hn).symm.le
  · exact (R.calibration_strict_minimum_lower hσ hb hω hq
      ⟨mul_nonneg hq.1.le hu.1,mul_le_of_le_one_right hq.1.le hu.2⟩ hn).le

end
end chebyshev2.Calibration.ReferenceData
