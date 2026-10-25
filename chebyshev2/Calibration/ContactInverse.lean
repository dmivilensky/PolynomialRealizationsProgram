import chebyshev2.Calibration.ContactMonotonicity
import Mathlib.Topology.Order.MonotoneContinuity

/-!
Article: chebyshev2, Theorem 3.2.
The contact inverse is constructed as an order isomorphism, rather than postulated as an extra
calibration input.
Use: `chebyshev2.Calibration.ReferenceData.contactInverse_continuous` feeds
`chebyshev2.Calibration.ReferenceData.contactValue_continuous` (contact Value continuous).
Proof chain: `chebyshev2.Calibration.ReferenceData.calibration` — chebyshev2, Theorem 3.2;
Constructed contact potential and calibrated reference.
-/
namespace chebyshev2.Calibration.ReferenceData
noncomputable section
open Set MeasureTheory Filter Real
open scoped Topology
set_option backward.isDefEq.respectTransparency false
variable (R : ReferenceData) {σ : ℝ} (hσ : 0 < σ)

/--
The stated quantitative bound `0 ≤ R.contact hσ x`.

Use: `chebyshev2.Calibration.ReferenceData.contact_image` uses this bound to establish
exact identity `R.contact hσ '' Ici (R.referenceSpeed.X 0)=Ico (0:ℝ) 2`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates
`chebyshev2.Calibration.ReferenceData.contact_strictMono`,
`chebyshev2.Calibration.ReferenceData.contact_left` with the arguments shown in the proof.
-/
theorem contact_nonneg {x : ℝ} (hx : R.referenceSpeed.X 0 ≤ x) : 0 ≤ R.contact hσ x := by
  have h := (R.contact_strictMono hσ).monotoneOn (show R.referenceSpeed.X 0 ∈ Ici (R.referenceSpeed.X 0) from by simp) hx hx
  simpa only [R.contact_left hσ] using h

/--
The stated quantitative bound `R.contact hσ x ≤ 2`.

Use: `chebyshev2.Calibration.ReferenceData.contact_lt_two` uses this bound to establish the
stated quantitative bound `R.contact hσ x < 2`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.

Proof: Pass the established inequalities to the limit using the displayed filter convergence.
Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation at an
arbitrary point in that intersection.
-/
theorem contact_le_two {x : ℝ} (hx : R.referenceSpeed.X 0 ≤ x) : R.contact hσ x ≤ 2 := by
  apply ge_of_tendsto (R.contact_limit hσ)
  filter_upwards [eventually_ge_atTop x] with y hy
  exact (R.contact_strictMono hσ).monotoneOn hx (hx.trans hy) hy

/--
The stated quantitative bound `R.contact hσ x < 2`.

Use: `chebyshev2.Calibration.ReferenceData.contact_image` uses this bound to establish
exact identity `R.contact hσ '' Ici (R.referenceSpeed.X 0)=Ico (0:ℝ) 2`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates
`chebyshev2.Calibration.ReferenceData.contact_strictMono`,
`chebyshev2.Calibration.ReferenceData.contact_le_two` with the arguments shown in the
proof.
-/
theorem contact_lt_two {x : ℝ} (hx : R.referenceSpeed.X 0 ≤ x) : R.contact hσ x < 2 := by
  have hp := (R.contact_strictMono hσ) hx (show x+1 ∈ Ici (R.referenceSpeed.X 0) by change R.referenceSpeed.X 0 ≤ x+1; linarith) (by linarith : x < x+1)
  exact hp.trans_le (R.contact_le_two hσ (by linarith : R.referenceSpeed.X 0 ≤ x+1))

/--
Exact identity `R.contact hσ '' Ici (R.referenceSpeed.X 0)=Ico (0:ℝ) 2`.

Use: `chebyshev2.Calibration.ReferenceData.contactIso` uses this identity in the displayed
construction of `contactIso`. Its inputs and component formulas are fixed by that definition.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates `chebyshev2.Calibration.ReferenceData.contact_nonneg`,
`chebyshev2.Calibration.ReferenceData.contact_lt_two`,
`chebyshev2.Calibration.ReferenceData.contact_limit` with the arguments shown in the proof.
-/
theorem contact_image : R.contact hσ '' Ici (R.referenceSpeed.X 0)=Ico (0:ℝ) 2 := by
  -- Use the identities/estimates `chebyshev2.Calibration.ReferenceData.contact_nonneg`,
  -- `chebyshev2.Calibration.ReferenceData.contact_lt_two`,
  -- `chebyshev2.Calibration.ReferenceData.contact_limit` with the arguments shown in the
  -- proof.
  ext h
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact ⟨R.contact_nonneg hσ hx,R.contact_lt_two hσ hx⟩
  · intro hh
    have he : ∀ᶠ x in atTop, h < R.contact hσ x := (R.contact_limit hσ).eventually (lt_mem_nhds hh.2)
    obtain ⟨b,hb,hval⟩ := ((eventually_ge_atTop (R.referenceSpeed.X 0)).and he).exists
    obtain ⟨x,hx,hc⟩ := intermediate_value_Icc hb (R.contact_continuous hσ).continuousOn
      (show h ∈ Icc (R.contact hσ (R.referenceSpeed.X 0)) (R.contact hσ b) by rw [R.contact_left hσ]; exact ⟨hh.1,hval.le⟩)
    exact ⟨x,hx.1,hc⟩

/--
Defines `contactIso` of type `Ici (R.referenceSpeed.X 0) ≃o Ico (0:ℝ) 2` by
`((R.contact_strictMono hσ).orderIso (R.contact hσ) (Ici (R.referenceSpeed.X 0))).trans
(Set.orderIsoOfEq _ _ (R.contact_image hσ))`.

Use: `chebyshev2.Calibration.ReferenceData.contactInverse` uses this definition in the
displayed construction of `contactInverse`. Its inputs and component formulas are fixed by that
definition.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.
-/
def contactIso : Ici (R.referenceSpeed.X 0) ≃o Ico (0:ℝ) 2 :=
  ((R.contact_strictMono hσ).orderIso (R.contact hσ) (Ici (R.referenceSpeed.X 0))).trans
    (Set.orderIsoOfEq _ _ (R.contact_image hσ))

/--
Exact identity `(R.contactIso hσ x : ℝ)=R.contact hσ x`.

Use: `chebyshev2.Calibration.ReferenceData.contact_inverse` rewrites with this identity to
establish exact identity `R.contact hσ (R.contactInverse hσ h)=h`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem contactIso_apply (x : Ici (R.referenceSpeed.X 0)) :
    (R.contactIso hσ x : ℝ)=R.contact hσ x := by simp [contactIso,StrictMonoOn.orderIso,Set.BijOn.equiv]

/--
Defines `contactInverse` of type `ℝ` by `(R.contactIso hσ).symm h`.

Use: `chebyshev2.Calibration.ReferenceData.contactInverse_continuous` uses this definition
to establish continuity of the displayed function: `Continuous (R.contactInverse hσ)`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.
-/
def contactInverse (h : Ico (0:ℝ) 2) : ℝ := (R.contactIso hσ).symm h

/--
The stated quantitative bound `R.referenceSpeed.X 0 ≤ R.contactInverse hσ h`.

Use: `chebyshev2.Calibration.ReferenceData.calibration_global_strict_minimum` uses this
bound to prove the bound `(R.calibration hσ hb hω).F q (R.contact hσ
(R.referenceSpeed.X q)) < (R.calibration hσ hb hω).F q h`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem contactInverse_mem (h : Ico (0:ℝ) 2) :
    R.referenceSpeed.X 0 ≤ R.contactInverse hσ h := ((R.contactIso hσ).symm h).property

/--
Exact identity `R.contact hσ (R.contactInverse hσ h)=h`.

Use: `chebyshev2.Calibration.ReferenceData.calibration_global_strict_minimum` uses this
identity to prove the bound `(R.calibration hσ hb hω).F q (R.contact hσ
(R.referenceSpeed.X q)) < (R.calibration hσ hb hω).F q h`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates `chebyshev2.Calibration.ReferenceData.contactIso_apply`
with the arguments shown in the proof.
-/
theorem contact_inverse (h : Ico (0:ℝ) 2) : R.contact hσ (R.contactInverse hσ h)=h := by
  have he := congrArg Subtype.val ((R.contactIso hσ).apply_symm_apply h)
  rw [R.contactIso_apply hσ] at he
  exact he

/--
Exact identity `R.contactInverse hσ (R.contactIso hσ x)=x`.

Use: `chebyshev2.Calibration.ReferenceData.potential_contact` uses this identity to
establish exact identity `R.potential hσ (R.contact hσ x)=R.filter hσ x+R.filter hσ (-x)`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem inverse_contact (x : Ici (R.referenceSpeed.X 0)) :
    R.contactInverse hσ (R.contactIso hσ x)=x :=
  congrArg Subtype.val ((R.contactIso hσ).symm_apply_apply x)

/--
Continuity of the displayed function: `Continuous (R.contactInverse hσ)`.

Use: `chebyshev2.Calibration.ReferenceData.contactValue_continuous` uses this continuity
result to establish continuity of the displayed function: `Continuous (R.contactValue hσ)`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem contactInverse_continuous : Continuous (R.contactInverse hσ) :=
  continuous_subtype_val.comp (R.contactIso hσ).toHomeomorph.symm.continuous

end
end chebyshev2.Calibration.ReferenceData
