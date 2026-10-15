import «2610.05164v2».Calibration.ContactInverse

/-!
Article: 2610.05164v2, Theorem 3.2.
The constructed potential g_circle of Theorem 3.2, its endpoint continuity, admissible bounds and
exact linear tail.
Use: `«2610.05164v2».Calibration.ReferenceData.calibration` feeds
`«2610.05164v2».Calibration.ReferenceData.selfConsistent_minimum_finite` (self Consistent minimum
finite).
-/
namespace «2610.05164v2».Calibration.ReferenceData
noncomputable section
open Set MeasureTheory Filter Real
open scoped Topology
set_option backward.isDefEq.respectTransparency false
variable (R : ReferenceData) {σ : ℝ} (hσ : 0 < σ)

/--
Defines `contactValue` of type `ℝ` by `R.filter hσ (R.contactInverse hσ h)+R.filter hσ
(-R.contactInverse hσ h)`.

Use: `«2610.05164v2».Calibration.ReferenceData.contactValue_bounds` uses this definition to
establish membership in the specified domain/enclosure: `R.contactValue hσ h ∈ Icc (0:ℝ)
(2-h)`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.
-/
def contactValue (h : Ico (0:ℝ) 2) : ℝ :=
  R.filter hσ (R.contactInverse hσ h)+R.filter hσ (-R.contactInverse hσ h)

/--
Defines `potential` of type `ℝ` by `if hh : h ∈ Ico (0:ℝ) 2 then R.contactValue hσ ⟨h,hh⟩ else
0`.

Use: `«2610.05164v2».Calibration.ReferenceData.calibration` uses this definition in the
displayed construction of `calibration`. Its inputs and component formulas are fixed by that
definition.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.
-/
def potential (h : ℝ) : ℝ := if hh : h ∈ Ico (0:ℝ) 2 then R.contactValue hσ ⟨h,hh⟩ else 0

/--
Exact identity `R.potential hσ 2=0`.

Use: `«2610.05164v2».Calibration.ReferenceData.potential_bounds` rewrites with this identity to
establish membership in the specified domain/enclosure: `R.potential hσ h ∈ Icc (0:ℝ) (2-h)`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem potential_two : R.potential hσ 2=0 := by simp [potential]

/--
Continuity of the displayed function: `Continuous (R.contactValue hσ)`.

Use: `«2610.05164v2».Calibration.ReferenceData.potential_continuousOn` uses this continuity
result to establish continuity on the stated domain: `ContinuousOn (R.potential hσ) (Icc (0:ℝ)
2)`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates `«2610.05164v2».Calibration.ReferenceData.filter_c1`,
`«2610.05164v2».Calibration.ReferenceData.contactInverse_continuous` with the arguments shown
in the proof.
-/
theorem contactValue_continuous : Continuous (R.contactValue hσ) :=
  ((R.filter_c1 hσ).continuous.comp (R.contactInverse_continuous hσ)).add
    ((R.filter_c1 hσ).continuous.comp (R.contactInverse_continuous hσ).neg)

/--
Membership in the specified domain/enclosure: `R.contactValue hσ h ∈ Icc (0:ℝ) (2-h)`.

Use: `«2610.05164v2».Calibration.ReferenceData.potential_bounds` uses this assertion to
establish membership in the specified domain/enclosure: `R.potential hσ h ∈ Icc (0:ℝ) (2-h)`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates `«2610.05164v2».Calibration.ReferenceData.filter_bounds`,
`«2610.05164v2».Calibration.ReferenceData.contact_inverse`,
`«2610.05164v2».Calibration.ReferenceData.coordinate_reflection` with the arguments shown in
the proof.
-/
theorem contactValue_bounds (h : Ico (0:ℝ) 2) :
    R.contactValue hσ h ∈ Icc (0:ℝ) (2-h) := by
  have hf := R.filter_bounds hσ (R.contactInverse hσ h)
  have hr := R.filter_bounds hσ (-R.contactInverse hσ h)
  rw [R.coordinate_reflection] at hr
  have hc := R.contact_inverse hσ h
  change R.referenceSpeed.q (R.contactInverse hσ h)-R.filter hσ (R.contactInverse hσ h)=h at hc
  exact ⟨add_nonneg hf.1 hr.1,by dsimp [contactValue]; linarith [hr.2]⟩

/--
Membership in the specified domain/enclosure: `R.potential hσ h ∈ Icc (0:ℝ) (2-h)`.

Use: `«2610.05164v2».Calibration.ReferenceData.calibration` uses this assertion in the
displayed construction of `calibration`. Its inputs and component formulas are fixed by that
definition.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Separate `h ∈ Ico (0:ℝ) 2` from its negation; prove the goal under each of these
mutually exclusive hypotheses.
-/
theorem potential_bounds {h : ℝ} (hh : h ∈ Icc (0:ℝ) 2) :
    R.potential hσ h ∈ Icc (0:ℝ) (2-h) := by
  by_cases hi : h ∈ Ico (0:ℝ) 2
  · rw [potential,dite_eq_left hi]
    exact R.contactValue_bounds hσ ⟨h,hi⟩
  · have he : h=2 := le_antisymm hh.2 (not_lt.mp (fun he => hi ⟨hh.1,he⟩))
    rw [he,R.potential_two hσ]
    norm_num

/--
Continuity on the stated domain: `ContinuousOn (R.potential hσ) (Icc (0:ℝ) 2)`.

Use: `«2610.05164v2».Calibration.ReferenceData.calibration` uses this continuity result in the
displayed construction of `calibration`. Its inputs and component formulas are fixed by that
definition.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Separate `h=2` from its negation; prove the goal under each of these mutually exclusive
hypotheses. Pass the established inequalities to the limit using the displayed filter
convergence. Intersect the eventual or almost-everywhere hypotheses, then prove the asserted
relation at an arbitrary point in that intersection.
-/
theorem potential_continuousOn : ContinuousOn (R.potential hσ) (Icc (0:ℝ) 2) := by
  -- Establish continuity hi before using the function at limits or in calculus arguments.
  have hi : ContinuousOn (R.potential hσ) (Ico (0:ℝ) 2) := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    have he : (Ico (0:ℝ) 2).domRestrict (R.potential hσ)=R.contactValue hσ := by
      funext h
      simp only [Set.domRestrict_apply,potential,dite_eq_left h.property]
    rw [he]
    exact R.contactValue_continuous hσ
  intro h hh
  by_cases he : h=2
  · subst h
    change Tendsto (R.potential hσ) (𝓝[Icc (0:ℝ) 2] 2) (𝓝 (R.potential hσ 2))
    rw [R.potential_two hσ]
    -- Record the convergence ht with its source filter and target limit before taking limits
    -- in the subsequent identities/bounds.
    have ht : Tendsto (fun t : ℝ => 2-t) (𝓝[Icc (0:ℝ) 2] 2) (𝓝 0) := by
      convert! ((continuous_const : Continuous (fun _ : ℝ => (2:ℝ))).sub
        continuous_id).continuousAt.continuousWithinAt.tendsto
          (x := (2:ℝ)) (s := Icc (0:ℝ) 2) using 1; norm_num
    apply squeeze_zero' (g := fun t : ℝ => 2-t) _ _ ht
    · filter_upwards [self_mem_nhdsWithin] with h hh
      exact (R.potential_bounds hσ hh).1
    · filter_upwards [self_mem_nhdsWithin] with h hh
      exact (R.potential_bounds hσ hh).2
  · have hlt : h < 2 := lt_of_le_of_ne hh.2 he
    apply (hi h ⟨hh.1,hlt⟩).mono_of_mem_nhdsWithin
    have hn : ∀ᶠ t in 𝓝[Icc (0:ℝ) 2] h, t < 2 :=
      (show ∀ᶠ t in 𝓝 h, t < 2 from Iio_mem_nhds hlt).filter_mono nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin,hn] with t ht ht2
    exact ⟨ht.1,ht2⟩

/--
Exact identity `R.potential hσ (R.contact hσ x)=R.filter hσ x+R.filter hσ (-x)`.

Use: `«2610.05164v2».Calibration.ReferenceData.calibration_contactFunctional` rewrites with
this identity to establish the identity `(R.calibration hσ hb hω).F q (R.contact hσ
x)=R.contactFunctional hσ q x`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates `«2610.05164v2».Calibration.ReferenceData.inverse_contact`,
`«2610.05164v2».Calibration.ReferenceData.contactIso_apply`,
`«2610.05164v2».Calibration.ReferenceData.contact_nonneg` with the arguments shown in the
proof.
-/
theorem potential_contact {x : ℝ} (hx : R.referenceSpeed.X 0 ≤ x) :
    R.potential hσ (R.contact hσ x)=R.filter hσ x+R.filter hσ (-x) := by
  -- Use the identities/estimates `«2610.05164v2».Calibration.ReferenceData.inverse_contact`,
  -- `«2610.05164v2».Calibration.ReferenceData.contactIso_apply`,
  -- `«2610.05164v2».Calibration.ReferenceData.contact_nonneg` with the arguments shown in the
  -- proof.
  let z : Ici (R.referenceSpeed.X 0) := ⟨x,hx⟩
  have he := R.inverse_contact hσ z
  have hv := R.contactIso_apply hσ z
  have hh : R.contact hσ x ∈ Ico (0:ℝ) 2 := ⟨R.contact_nonneg hσ hx,R.contact_lt_two hσ hx⟩
  rw [potential,dite_eq_left hh]
  have hh' : (⟨R.contact hσ x,hh⟩ : Ico (0:ℝ) 2)=R.contactIso hσ z := Subtype.ext hv.symm
  rw [hh']
  dsimp only [contactValue]
  rw [he]

/--
Exact identity `R.potential hσ h=2-h`.

Use: `«2610.05164v2».Calibration.ReferenceData.J_tail` uses this identity to establish the
identity stated in that declaration.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Separate `h=2` from its negation; prove the goal under each of these mutually exclusive
hypotheses. Assume the failure of the desired conclusion and derive a contradiction from the
available bounds/identities.
-/
theorem potential_tail {h : ℝ} (hh : h ∈ Icc (0:ℝ) 2)
    (ht : R.contact hσ (R.referenceSpeed.X 2) ≤ h) : R.potential hσ h=2-h := by
  -- Separate `h=2` from its negation; prove the goal under each of these mutually exclusive
  -- hypotheses.
  by_cases he : h=2
  · rw [he,R.potential_two hσ,sub_self]
  · have hi : h ∈ Ico (0:ℝ) 2 := ⟨hh.1,lt_of_le_of_ne hh.2 he⟩
    let x := R.contactInverse hσ ⟨h,hi⟩
    have hx : R.referenceSpeed.X 2 ≤ x := by
      by_contra hn
      have hp := (R.contact_strictMono hσ) (R.contactInverse_mem hσ ⟨h,hi⟩)
        R.referenceSpeed.X_endpoint_order.le (not_le.mp hn)
      rw [R.contact_inverse hσ ⟨h,hi⟩] at hp
      linarith
    have hleft : -x ≤ R.referenceSpeed.X 0 := by
      have hr := R.X_reflection 0
      norm_num only [sub_zero] at hr
      linarith
    have hc := R.contact_inverse hσ ⟨h,hi⟩
    change R.referenceSpeed.q x-R.filter hσ x=h at hc
    rw [R.referenceSpeed.q_two_right hx] at hc
    rw [potential,dite_eq_left hi]
    change R.filter hσ x+R.filter hσ (-x)=2-h
    rw [R.filter_zero_left hσ hleft,add_zero]
    linarith

/--
Actual Definition 4 data from the constructed contact potential.

Use: `«2610.05164v2».Calibration.ReferenceData.J_contact_half_integral` uses this definition to
establish the identity stated in that declaration.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.
-/
def calibration {b ω : ℝ} (hb : 0 < b) (hω : 0 ≤ ω) : Data where
  sigma := σ
  sigma_positive := hσ
  b := b
  b_positive := hb
  omega := ω
  omega_nonneg := hω
  g := R.potential hσ
  continuous := R.potential_continuousOn hσ
  bounds := fun _ hh => R.potential_bounds hσ hh

end
end «2610.05164v2».Calibration.ReferenceData
