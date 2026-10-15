import «2610.05164v2».Calibration.ContactMinimum
import «2610.05164v2».Calibration.ContactSymmetry

/-!
Article: 2610.05164v2, Theorem 3.2.
The global contact minimum on [0,2], not only the interval defining Gamma.
Use: `«2610.05164v2».Calibration.ReferenceData.calibration_Gamma_reflection` feeds
`«2610.05164v2».Calibration.ReferenceData.J_contact_half_integral` (J contact half integral).
Proof chain: `«2610.05164v2».Calibration.ReferenceData.calibration_constant_normalized` —
2610.05164v2, Theorem 3.2; Constructed contact potential and calibrated reference.
-/
namespace «2610.05164v2».Calibration.ReferenceData
noncomputable section
open Set Real
set_option backward.isDefEq.respectTransparency false
variable (R : ReferenceData) {σ : ℝ} (hσ : 0 < σ)

/--
The stated quantitative bound `(R.calibration hσ hb hω).F q q ≤ (R.calibration hσ hb hω).F q
h`.

Use: `«2610.05164v2».Calibration.ReferenceData.calibration_global_strict_minimum_lower` uses
this bound to prove the bound `(R.calibration hσ hb hω).F q (R.contact
hσ (R.referenceSpeed.X q)) < (R.calibration hσ hb hω).F q h`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates
`«2610.05164v2».Calibration.ReferenceData.potential_plus_id_monotone`,
`«2610.05164v2».Calibration.ReferenceData.potential_bounds`,
`«2610.05164v2».Calibration.beyond_diagonal` with the arguments shown in the proof.
-/
theorem calibration_beyond_diagonal {b ω q h : ℝ} (hb : 0 < b) (hω : 0 ≤ ω)
    (hq : q ∈ Icc (0:ℝ) 2) (hh : h ∈ Icc q 2) :
    (R.calibration hσ hb hω).F q q ≤ (R.calibration hσ hb hω).F q h := by
  -- Use the identities/estimates
  -- `«2610.05164v2».Calibration.ReferenceData.potential_plus_id_monotone`,
  -- `«2610.05164v2».Calibration.ReferenceData.potential_bounds`,
  -- `«2610.05164v2».Calibration.beyond_diagonal` with the arguments shown in the proof.
  have hh2 : h ∈ Icc (0:ℝ) 2 := ⟨hq.1.trans hh.1,hh.2⟩
  have hm := R.potential_plus_id_monotone hσ hq hh2 hh.1
  have hg := R.potential_bounds hσ hh2
  have hG := R.potential_bounds hσ hq
  have hbeyond := beyond_diagonal hσ hq hG.1 hg.1 (sub_nonneg.mpr hh.1)
    (show R.potential hσ q-(h-q) ≤ R.potential hσ h by linarith)
    (R.potential_quadratic_threshold hσ hq)
  dsimp only [Data.F]
  rw [(R.calibration hσ hb hω).potential_eq hq,
    (R.calibration hσ hb hω).potential_eq hh2]
  change (2*(q-q)^2-(q^2-2*q)*R.potential hσ q)/(2+σ*R.potential hσ q) ≤
    (2*(q-h)^2-(q^2-2*h)*R.potential hσ h)/(2+σ*R.potential hσ h)
  convert! hbeyond using 1 <;> congr 1 <;> unfold Q <;> ring

/--
The stated quantitative bound `(R.calibration hσ hb hω).F q (R.contact hσ (R.referenceSpeed.X
q)) < (R.calibration hσ hb hω).F q h`.

Use: `«2610.05164v2».Calibration.ReferenceData.calibration_global_strict_minimum` uses this
bound to prove the bound `(R.calibration hσ hb hω).F q (R.contact hσ
(R.referenceSpeed.X q)) < (R.calibration hσ hb hω).F q h`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Separate `h ≤ q` from its negation; prove the goal under each of these mutually
exclusive hypotheses.
-/
theorem calibration_global_strict_minimum_lower {b ω q h : ℝ} (hb : 0 < b) (hω : 0 ≤ ω)
    (hq : q ∈ Ioc (0:ℝ) 1) (hh : h ∈ Icc (0:ℝ) 2)
    (hne : h ≠ R.contact hσ (R.referenceSpeed.X q)) :
    (R.calibration hσ hb hω).F q (R.contact hσ (R.referenceSpeed.X q)) <
      (R.calibration hσ hb hω).F q h := by
  -- Separate `h ≤ q` from its negation; prove the goal under each of these mutually exclusive
  -- hypotheses.
  by_cases hle : h ≤ q
  · exact R.calibration_strict_minimum_lower hσ hb hω hq ⟨hh.1,hle⟩ hne
  · have hq2 : q ∈ Icc (0:ℝ) 2 := ⟨hq.1.le,by linarith [hq.2]⟩
    have hx : R.referenceSpeed.X 0 < R.referenceSpeed.X q :=
      R.referenceSpeed.X_strictMono (by norm_num) hq2 hq.1
    have hf := R.filter_positive hσ hx
    have hn : q ≠ R.contact hσ (R.referenceSpeed.X q) := by
      change q ≠ R.referenceSpeed.q (R.referenceSpeed.X q)-R.filter hσ (R.referenceSpeed.X q)
      rw [R.referenceSpeed.q_X hq2]
      linarith
    exact (R.calibration_strict_minimum_lower hσ hb hω hq ⟨hq.1.le,le_rfl⟩ hn).trans_le
      (R.calibration_beyond_diagonal hσ hb hω hq2 ⟨(not_le.mp hle).le,hh.2⟩)

/--
The stated quantitative bound `(R.calibration hσ hb hω).F q h < (R.calibration hσ hb hω).F q
t`.

Use: `«2610.05164v2».Calibration.ReferenceData.calibration_global_strict_minimum` uses this
bound to prove the bound `(R.calibration hσ hb hω).F q (R.contact hσ
(R.referenceSpeed.X q)) < (R.calibration hσ hb hω).F q h`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates `«2610.05164v2».Calibration.Data.potential_eq`,
`«2610.05164v2».Calibration.ReferenceData.potential_tail`,
`«2610.05164v2».Calibration.Data.F_tail_value` with the arguments shown in the proof.
-/
theorem calibration_tail_strict {b ω q h t : ℝ} (hb : 0 < b) (hω : 0 ≤ ω)
    (hq : q < 2) (hh : h ∈ Icc (0:ℝ) 2) (ht : t ∈ Icc (0:ℝ) 2)
    (hl : R.contact hσ (R.referenceSpeed.X 2) ≤ h) (hht : h < t) :
    (R.calibration hσ hb hω).F q h < (R.calibration hσ hb hω).F q t := by
  -- Use the identities/estimates `«2610.05164v2».Calibration.Data.potential_eq`,
  -- `«2610.05164v2».Calibration.ReferenceData.potential_tail`,
  -- `«2610.05164v2».Calibration.Data.F_tail_value` with the arguments shown in the proof.
  let C := R.calibration hσ hb hω
  have hg : C.potential h=2-h := by
    rw [C.potential_eq hh]
    exact R.potential_tail hσ hh hl
  have htg : C.potential t=2-t := by
    rw [C.potential_eq ht]
    exact R.potential_tail hσ ht (hl.trans hht.le)
  rw [C.F_tail_value hg,C.F_tail_value htg]
  apply (div_lt_div_iff₀ (by change 0<2+σ*(2-h); nlinarith [mul_nonneg hσ.le (sub_nonneg.mpr hh.2)])
    (by change 0<2+σ*(2-t); nlinarith [mul_nonneg hσ.le (sub_nonneg.mpr ht.2)])).2
  have hp : 0 < (t-h)*(2-q)^2*(2+2*σ) := by
    apply mul_pos (mul_pos (sub_pos.mpr hht) (sq_pos_of_pos (sub_pos.mpr hq)))
    linarith
  change h*(2-q)^2*(2+σ*(2-t)) < t*(2-q)^2*(2+σ*(2-h))
  nlinarith

/--
The stated quantitative bound `(R.calibration hσ hb hω).F q (R.contact hσ (R.referenceSpeed.X
q)) < (R.calibration hσ hb hω).F q (R.contact hσ x)`.

Use: `«2610.05164v2».Calibration.ReferenceData.calibration_global_strict_minimum` uses this
bound to prove the bound `(R.calibration hσ hb hω).F q (R.contact hσ
(R.referenceSpeed.X q)) < (R.calibration hσ hb hω).F q h`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates `«2610.05164v2».PrescribedSpeed.SpeedData.X_strictMono`,
`«2610.05164v2».Calibration.ReferenceData.X_reflection`,
`«2610.05164v2».Calibration.ReferenceData.contact_strictMono` with the arguments shown in the
proof.
-/
theorem calibration_physical_strict_minimum_upper {b ω q x : ℝ} (hb : 0 < b) (hω : 0 ≤ ω)
    (hq : q ∈ Ioo (1:ℝ) 2)
    (hx : x ∈ Icc (R.referenceSpeed.X 0) (R.referenceSpeed.X 2))
    (hne : x ≠ R.referenceSpeed.X q) :
    (R.calibration hσ hb hω).F q (R.contact hσ (R.referenceSpeed.X q)) <
      (R.calibration hσ hb hω).F q (R.contact hσ x) := by
  -- Use the identities/estimates `«2610.05164v2».PrescribedSpeed.SpeedData.X_strictMono`,
  -- `«2610.05164v2».Calibration.ReferenceData.X_reflection`,
  -- `«2610.05164v2».Calibration.ReferenceData.contact_strictMono` with the arguments shown in
  -- the proof.
  have hq2 : q ∈ Icc (0:ℝ) 2 := ⟨by linarith [hq.1],hq.2.le⟩
  have hqs : 2-q ∈ Ioc (0:ℝ) 1 := ⟨by linarith [hq.2],by linarith [hq.1]⟩
  have hstar : R.referenceSpeed.X q ∈ Icc (R.referenceSpeed.X 0) (R.referenceSpeed.X 2) :=
    ⟨R.referenceSpeed.X_strictMono.monotoneOn (by norm_num) hq2 hq2.1,
      R.referenceSpeed.X_strictMono.monotoneOn hq2 (by norm_num) hq2.2⟩
  have hX := R.X_reflection 0
  norm_num only [sub_zero] at hX
  have hnx : R.referenceSpeed.X 0 ≤ -x := by linarith [hx.2]
  have hXs : R.referenceSpeed.X 0 ≤ R.referenceSpeed.X (2-q) :=
    R.referenceSpeed.X_strictMono.monotoneOn (by norm_num)
      ⟨hqs.1.le,by linarith [hqs.2]⟩ hqs.1.le
  have hn : R.contact hσ (-x) ≠ R.contact hσ (R.referenceSpeed.X (2-q)) := by
    intro he
    have hi := (R.contact_strictMono hσ).injOn hnx hXs he
    rw [R.X_reflection] at hi
    exact hne (by linarith)
  rw [R.calibration_F_reflection hσ hb hω hstar,R.calibration_F_reflection hσ hb hω hx,
    ← R.X_reflection q]
  exact R.calibration_global_strict_minimum_lower hσ hb hω hqs
    (R.involution_contact_mem hσ hx) hn

/--
The stated quantitative bound `(R.calibration hσ hb hω).F q (R.contact hσ (R.referenceSpeed.X
q)) < (R.calibration hσ hb hω).F q h`.

Use: `«2610.05164v2».Calibration.ReferenceData.calibration_Gamma` uses this bound to establish
the precise assertion is `(R.calibration hσ hb hω).Gamma q= (R.calibration hσ hb hω).F q
(R.contact hσ (R.referenceSpeed.X q))`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Separate `q ≤ 1` from its negation; prove the goal under each of these mutually
exclusive hypotheses. Assume the failure of the desired conclusion and derive a contradiction
from the available bounds/identities.
-/
theorem calibration_global_strict_minimum {b ω q h : ℝ} (hb : 0 < b) (hω : 0 ≤ ω)
    (hq : q ∈ Ioo (0:ℝ) 2) (hh : h ∈ Icc (0:ℝ) 2)
    (hne : h ≠ R.contact hσ (R.referenceSpeed.X q)) :
    (R.calibration hσ hb hω).F q (R.contact hσ (R.referenceSpeed.X q)) <
      (R.calibration hσ hb hω).F q h := by
  -- Separate `q ≤ 1` from its negation; prove the goal under each of these mutually exclusive
  -- hypotheses.
  by_cases hlow : q ≤ 1
  · exact R.calibration_global_strict_minimum_lower hσ hb hω ⟨hq.1,hlow⟩ hh hne
  · have hqu : q ∈ Ioo (1:ℝ) 2 := ⟨not_le.mp hlow,hq.2⟩
    have hbound := R.contact_lt_two hσ R.referenceSpeed.X_endpoint_order.le
    by_cases htail : h ≤ R.contact hσ (R.referenceSpeed.X 2)
    · have hh' : h ∈ Ico (0:ℝ) 2 := ⟨hh.1,htail.trans_lt hbound⟩
      let x := R.contactInverse hσ ⟨h,hh'⟩
      have hl := R.contactInverse_mem hσ ⟨h,hh'⟩
      have hc : R.contact hσ x=h := R.contact_inverse hσ _
      have hr : x ≤ R.referenceSpeed.X 2 := by
        by_contra hn
        have hm := R.contact_strictMono hσ R.referenceSpeed.X_endpoint_order.le hl (not_le.mp hn)
        rw [hc] at hm
        linarith
      have hn : x ≠ R.referenceSpeed.X q := by
        intro he
        rw [he] at hc
        exact hne hc.symm
      have hm := R.calibration_physical_strict_minimum_upper hσ hb hω hqu ⟨hl,hr⟩ hn
      rwa [hc] at hm
    · have hq2 : q ∈ Icc (0:ℝ) 2 := ⟨hq.1.le,hq.2.le⟩
      have hXq := R.referenceSpeed.X_strictMono hq2 (by norm_num) hq.2
      have hn : R.referenceSpeed.X 2 ≠ R.referenceSpeed.X q := ne_of_gt hXq
      have hm := R.calibration_physical_strict_minimum_upper hσ hb hω hqu
        ⟨R.referenceSpeed.X_endpoint_order.le,le_rfl⟩ hn
      exact hm.trans (R.calibration_tail_strict hσ hb hω hq.2
        ⟨R.contact_nonneg hσ R.referenceSpeed.X_endpoint_order.le,hbound.le⟩ hh le_rfl (not_le.mp htail))

/--
The precise assertion is `(R.calibration hσ hb hω).Gamma q= (R.calibration hσ hb hω).F q
(R.contact hσ (R.referenceSpeed.X q))`.

Use: `«2610.05164v2».Calibration.ReferenceData.calibration_Gamma_value` rewrites with this
identity to establish the identity stated in that declaration.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Separate `q*u=R.contact hσ (R.referenceSpeed.X q)` from its negation; prove the goal
under each of these mutually exclusive hypotheses.
-/
theorem calibration_Gamma {b ω q : ℝ} (hb : 0 < b) (hω : 0 ≤ ω)
    (hq : q ∈ Ioo (0:ℝ) 2) :
    (R.calibration hσ hb hω).Gamma q=
      (R.calibration hσ hb hω).F q (R.contact hσ (R.referenceSpeed.X q)) := by
  -- Separate `q*u=R.contact hσ (R.referenceSpeed.X q)` from its negation; prove the goal under
  -- each of these mutually exclusive hypotheses.
  let C := R.calibration hσ hb hω
  have hh := R.contact_at_X_bounds hσ ⟨hq.1.le,hq.2.le⟩
  apply le_antisymm (C.Gamma_le_state hq.1.le hh)
  obtain ⟨u,hu,he⟩ := C.Gamma_attained q
  rw [← he]
  by_cases hn : q*u=R.contact hσ (R.referenceSpeed.X q)
  · exact (congrArg (C.F q) hn).symm.le
  · exact (R.calibration_global_strict_minimum hσ hb hω hq
      ⟨mul_nonneg hq.1.le hu.1,(mul_le_of_le_one_right hq.1.le hu.2).trans hq.2.le⟩ hn).le

/--
Theorem 3.2, equation (19), for the actually constructed contact potential.

Use: `«2610.05164v2».Calibration.ReferenceData.calibration_Gamma_reflection` rewrites with this
identity to establish the identity `(R.calibration hσ hb hω).Gamma (2-q)=(R.calibration hσ hb
hω).Gamma q`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates
`«2610.05164v2».Calibration.ReferenceData.calibration_Gamma`,
`«2610.05164v2».PrescribedSpeed.SpeedData.X_strictMono`,
`«2610.05164v2».Calibration.ReferenceData.calibration_contactFunctional` with the arguments
shown in the proof.
-/
theorem calibration_Gamma_value {b ω q : ℝ} (hb : 0 < b) (hω : 0 ≤ ω)
    (hq : q ∈ Ioo (0:ℝ) 2) :
    (R.calibration hσ hb hω).Gamma q=
      (Q q*(R.filter hσ (R.referenceSpeed.X q)+R.filter hσ (-R.referenceSpeed.X q))-
        2*R.filter hσ (R.referenceSpeed.X q)*R.filter hσ (-R.referenceSpeed.X q))/
      (2+σ*(R.filter hσ (R.referenceSpeed.X q)+R.filter hσ (-R.referenceSpeed.X q))) := by
  -- Use the identities/estimates `«2610.05164v2».Calibration.ReferenceData.calibration_Gamma`,
  -- `«2610.05164v2».PrescribedSpeed.SpeedData.X_strictMono`,
  -- `«2610.05164v2».Calibration.ReferenceData.calibration_contactFunctional` with the
  -- arguments shown in the proof.
  rw [R.calibration_Gamma hσ hb hω hq]
  have hq2 : q ∈ Icc (0:ℝ) 2 := ⟨hq.1.le,hq.2.le⟩
  have hx := R.referenceSpeed.X_strictMono.monotoneOn (by norm_num : (0:ℝ) ∈ Icc (0:ℝ) 2) hq2 hq.1.le
  rw [R.calibration_contactFunctional hσ hb hω q hx]
  dsimp only [contactFunctional,contact]
  rw [R.referenceSpeed.q_X hq2]
  congr 1
  unfold Q
  ring

/--
Exact identity `(R.calibration hσ hb hω).Gamma (2-q)=(R.calibration hσ hb hω).Gamma q`.

Use: `«2610.05164v2».Calibration.ReferenceData.J_contact_half_integral` rewrites with this
identity to establish the identity stated in that declaration.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates `«2610.05164v2».Calibration.Data.Gamma_two`,
`«2610.05164v2».Calibration.Data.Gamma_zero`,
`«2610.05164v2».Calibration.ReferenceData.calibration_Gamma_value` with the arguments shown in
the proof.
-/
theorem calibration_Gamma_reflection {b ω : ℝ} (hb : 0 < b) (hω : 0 ≤ ω) (q : ℝ)
    (hq : q ∈ Icc (0:ℝ) 2) :
    (R.calibration hσ hb hω).Gamma (2-q)=(R.calibration hσ hb hω).Gamma q := by
  -- Use the identities/estimates `«2610.05164v2».Calibration.Data.Gamma_two`,
  -- `«2610.05164v2».Calibration.Data.Gamma_zero`,
  -- `«2610.05164v2».Calibration.ReferenceData.calibration_Gamma_value` with the arguments
  -- shown in the proof.
  rcases eq_or_lt_of_le hq.1 with he | hp
  · rw [← he]
    simp only [sub_zero,Data.Gamma_zero,Data.Gamma_two]
  · rcases eq_or_lt_of_le hq.2 with he | ht
    · rw [he]
      simp only [sub_self,Data.Gamma_zero,Data.Gamma_two]
    · rw [R.calibration_Gamma_value hσ hb hω ⟨by linarith,by linarith⟩,
        R.calibration_Gamma_value hσ hb hω ⟨hp,ht⟩,R.X_reflection,neg_neg,Q_reflection]
      congr 1 <;> ring

end
end «2610.05164v2».Calibration.ReferenceData
