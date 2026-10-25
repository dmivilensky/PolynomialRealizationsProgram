import chebyshev2.Comparison.Profile
import chebyshev2.Comparison.GroundReflection

/-!
Article: chebyshev2, Lemma 10.
Definition 10's full profile class: the actual compactly supported prescribed-speed density,
including endpoint continuity.
Use: `chebyshev2.Comparison.Profile.density_properties` feeds
`chebyshev2.Calibration.ReferenceData.density_properties` (density properties).
Proof chain: `chebyshev2.Calibration.ReferenceData.contact_image` — chebyshev2, Theorem 3.2;
Constructed contact potential and calibrated reference.
-/
namespace chebyshev2.Comparison.Profile
noncomputable section
open Set MeasureTheory Filter Real chebyshev2.Calibration chebyshev2.PrescribedSpeed chebyshev2.GroundState chebyshev2.Filters
set_option backward.isDefEq.respectTransparency false
variable {κ : ℝ} (P : chebyshev2.Comparison.Profile κ) (hκ : 0 < κ)

/--
The stated quantitative bound `(P.amplitude q)^3 ≤ P.C*Q q`.

Use: `chebyshev2.Comparison.Profile.amplitude_two` uses this bound to establish exact
identity `P.amplitude 2=0`.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates `chebyshev2.Calibration.Q_positive` with the arguments
shown in the proof.
-/
theorem cube_bound {q : ℝ} (hq : q ∈ Icc (0:ℝ) 2) : (P.amplitude q)^3 ≤ P.C*Q q := by
  -- Use the identities/estimates `chebyshev2.Calibration.Q_positive` with the arguments
  -- shown in the proof.
  have h : ∀ q ∈ Ioo (0:ℝ) 2, (P.amplitude q)^3 ≤ P.C*Q q := by
    intro q hq
    have hv := P.positive q hq
    have hd := P.speed_positive q hq
    have hQ := Q_positive hq
    have h1 : 0 ≤ (P.amplitude q)^2/(κ*(P.amplitude q)^2-Q q) := by positivity
    have h2 : 0 ≤ Q q/((κ*(P.amplitude q)^2-Q q)*P.amplitude q) := by positivity
    have hb := P.bound q hq
    apply (div_le_iff₀ hQ).mp
    linarith
  apply le_on_closure h
  · rw [closure_Ioo (by norm_num : (0:ℝ) ≠ 2)]
    exact P.continuous.pow 3
  · rw [closure_Ioo (by norm_num : (0:ℝ) ≠ 2)]
    unfold Q
    fun_prop
  · simpa only [closure_Ioo (by norm_num : (0:ℝ) ≠ 2)] using hq

/--
Exact identity `P.amplitude 0=0`.

Use: `chebyshev2.Comparison.Profile.density_formula` rewrites with this identity to
establish exact identity `P.density hκ x=(P.amplitude ((P.speedData hκ).q x))^2`.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.

Proof: Assume the failure of the desired conclusion and derive a contradiction from the
available bounds/identities.
-/
theorem amplitude_zero : P.amplitude 0=0 := by
  have hb := P.cube_bound (q := 0) (by norm_num)
  have hn := P.nonneg 0 (by norm_num)
  norm_num [Q] at hb
  by_contra he
  have hp := pow_pos (lt_of_le_of_ne hn (Ne.symm he)) 3
  linarith

/--
Exact identity `P.amplitude 2=0`.

Use: `chebyshev2.Comparison.Profile.density_formula` rewrites with this identity to
establish exact identity `P.density hκ x=(P.amplitude ((P.speedData hκ).q x))^2`.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.

Proof: Assume the failure of the desired conclusion and derive a contradiction from the
available bounds/identities.
-/
theorem amplitude_two : P.amplitude 2=0 := by
  have hb := P.cube_bound (q := 2) (by norm_num)
  have hn := P.nonneg 2 (by norm_num)
  norm_num [Q] at hb
  by_contra he
  have hp := pow_pos (lt_of_le_of_ne hn (Ne.symm he)) 3
  linarith

/--
Defines `extendedAmplitude` of type `ℝ` by `P.amplitude (max 0 (min 2 q))`.

Use: `chebyshev2.Comparison.Profile.extendedAmplitude_eq` rewrites with this definition to
establish exact identity `P.extendedAmplitude q=P.amplitude q`.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.
-/
def extendedAmplitude (q : ℝ) : ℝ := P.amplitude (max 0 (min 2 q))

/--
Exact identity `P.extendedAmplitude q=P.amplitude q`.

Use: `chebyshev2.Comparison.Profile.speed_eq` rewrites with this identity to establish
exact identity `P.speed q=κ*(P.amplitude q)^2-Q q`.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem extendedAmplitude_eq {q : ℝ} (hq : q ∈ Icc (0:ℝ) 2) :
    P.extendedAmplitude q=P.amplitude q := by simp only [extendedAmplitude,min_eq_right hq.2,max_eq_right hq.1]

/--
Continuity of the displayed function: `Continuous P.extendedAmplitude`.

Use: `chebyshev2.Comparison.Profile.speedData` uses this continuity result in the displayed
construction of `speedData`. Its inputs and component formulas are fixed by that definition.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates `chebyshev2.Calibration.Data.clamp_mem` with the
arguments shown in the proof.
-/
theorem extendedAmplitude_continuous : Continuous P.extendedAmplitude :=
  P.continuous.comp_continuous (continuous_const.max (continuous_const.min continuous_id)) Data.clamp_mem

/--
Defines `speed` of type `ℝ` by `κ*(P.extendedAmplitude q)^2-Q q`.

Use: `chebyshev2.Comparison.Profile.density_formula` uses this definition to establish
exact identity `P.density hκ x=(P.amplitude ((P.speedData hκ).q x))^2`.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.
-/
def speed (q : ℝ) : ℝ := κ*(P.extendedAmplitude q)^2-Q q

/--
Exact identity `P.speed q=κ*(P.amplitude q)^2-Q q`.

Use: `chebyshev2.Comparison.Profile.density_formula` rewrites with this identity to
establish exact identity `P.density hκ x=(P.amplitude ((P.speedData hκ).q x))^2`.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates `chebyshev2.Comparison.Profile.extendedAmplitude_eq`
with the arguments shown in the proof.
-/
theorem speed_eq {q : ℝ} (hq : q ∈ Icc (0:ℝ) 2) :
    P.speed q=κ*(P.amplitude q)^2-Q q := by rw [speed,P.extendedAmplitude_eq hq]

/--
Constructs `speedData` of type `SpeedData` by the displayed record fields. Data fields specify
the construction; proof fields discharge its required properties.

Use: `chebyshev2.Comparison.Profile.density_bounded` uses this definition to establish
constructs witnesses with the exact properties `∃ B : ℝ, 0 ≤ B ∧ ∀ x, P.density hκ x ≤ B`.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.
-/
def speedData : SpeedData where
  D := P.speed
  measurable := ((P.extendedAmplitude_continuous.pow 2).const_mul κ |>.sub
    (by unfold Q; fun_prop)).measurable
  positive := fun q hq => by rw [P.speed_eq ⟨hq.1.le,hq.2.le⟩]; exact P.speed_positive q hq
  B := κ*(max (Classical.choose (isCompact_Icc.bddAbove_image P.continuous)) 1)^2+1
  bound_positive := by positivity
  bound := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with q hq
    have hv := P.nonneg q ⟨hq.1.le,hq.2.le⟩
    have hqM := Classical.choose_spec (isCompact_Icc.bddAbove_image P.continuous)
      (mem_image_of_mem P.amplitude ⟨hq.1.le,hq.2.le⟩)
    have hle := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hv
      (hqM.trans (le_max_left _ (1:ℝ))) 2) hκ.le
    rw [P.speed_eq ⟨hq.1.le,hq.2.le⟩]
    have hQ := Q_positive hq
    linarith
  reciprocal_integrable := P.reciprocal_integrable.congr (by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with q hq
    rw [P.speed_eq ⟨hq.1.le,hq.2.le⟩])

/--
Defines `density` of type `ℝ → ℝ` by `(P.speedData hκ).density κ`.

Use: `chebyshev2.Comparison.Profile.density_continuous` uses this definition to establish
continuity of the displayed function: `Continuous (P.density hκ)`.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.
-/
def density : ℝ → ℝ := (P.speedData hκ).density κ

/--
Exact identity `P.density hκ x=(P.amplitude ((P.speedData hκ).q x))^2`.

Use: `chebyshev2.Comparison.Profile.density_bounded` rewrites with this identity to
establish constructs witnesses with the exact properties `∃ B : ℝ, 0 ≤ B ∧ ∀ x, P.density hκ x
≤ B`.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.

Proof: Separate `x ∈ Ioo (S.X 0) (S.X 2)` from its negation; prove the goal under each of these
mutually exclusive hypotheses. Clear the denominators using the available nonzero hypotheses,
then verify the remaining algebraic identity.
-/
theorem density_formula (x : ℝ) : P.density hκ x=(P.amplitude ((P.speedData hκ).q x))^2 := by
  -- Separate `x ∈ Ioo (S.X 0) (S.X 2)` from its negation; prove the goal under each of these
  -- mutually exclusive hypotheses.
  let S := P.speedData hκ
  by_cases hx : x ∈ Ioo (S.X 0) (S.X 2)
  · rw [density,SpeedData.density,indicator_of_mem hx]
    change (P.speed (S.q x)+S.q x*(2-S.q x))/κ=_
    rw [P.speed_eq (S.q_mem x)]
    unfold Q
    field_simp
    ring
  · change S.density κ x=_
    rw [S.density_zero_outside κ hx]
    rcases le_or_gt x (S.X 0) with hl | hl
    · rw [S.q_zero_left hl,P.amplitude_zero,zero_pow (by norm_num : (2:ℕ) ≠ 0)]
    · have hr : S.X 2 ≤ x := not_lt.mp (fun hr => hx ⟨hl,hr⟩)
      rw [S.q_two_right hr,P.amplitude_two,zero_pow (by norm_num : (2:ℕ) ≠ 0)]

/--
Continuity of the displayed function: `Continuous (P.density hκ)`.

Use: `chebyshev2.Calibration.ReferenceData.density_continuous` uses this continuity result
to establish continuity of the displayed function: `Continuous R.density`.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem density_continuous : Continuous (P.density hκ) := by
  have he : P.density hκ=fun x => (P.amplitude ((P.speedData hκ).q x))^2 :=
    funext (P.density_formula hκ)
  rw [he]
  exact (P.continuous.comp_continuous (P.speedData hκ).q_continuous (P.speedData hκ).q_mem).pow 2

/--
Constructs witnesses with the exact properties `∃ B : ℝ, 0 ≤ B ∧ ∀ x, P.density hκ x ≤ B`.

Use: `chebyshev2.Calibration.ReferenceData.density_bounded` uses this bound to establish
constructs witnesses with the exact properties `∃ B : ℝ, 0 ≤ B ∧ ∀ x, R.density x ≤ B`.

Article: chebyshev2, Proposition 5 via
`chebyshev2.Calibration.ReferenceData.selfConsistent_attainment`.

Proof: Use the identities/estimates `chebyshev2.Comparison.Profile.density_formula`,
`chebyshev2.PrescribedSpeed.SpeedData.q_mem` with the arguments shown in the proof.
-/
theorem density_bounded : ∃ B : ℝ, 0 ≤ B ∧ ∀ x, P.density hκ x ≤ B := by
  obtain ⟨M,hM⟩ := isCompact_Icc.bddAbove_image P.continuous
  refine ⟨(max M 0)^2,sq_nonneg _,?_⟩
  intro x
  rw [P.density_formula hκ]
  exact pow_le_pow_left₀ (P.nonneg _ ((P.speedData hκ).q_mem x))
    ((hM (mem_image_of_mem _ ((P.speedData hκ).q_mem x))).trans (le_max_left _ _)) 2

/--
Integrability of the displayed function: `Integrable (P.density hκ) ∧ (∀ x, 0 ≤ P.density hκ x)
∧ HasCompactSupport (P.density hκ) ∧ groundParameter ((P.speedData hκ).density_integrable hκ)
((P.speedData hκ).density_nonneg hκ)=κ`.

Use: `chebyshev2.Calibration.ReferenceData.density_properties` uses this integrability
result to establish the integrability result stated in that declaration.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates
`chebyshev2.PrescribedSpeed.SpeedData.density_integrable`,
`chebyshev2.PrescribedSpeed.SpeedData.density_nonneg`,
`chebyshev2.PrescribedSpeed.SpeedData.density_compact_support` with the arguments shown in
the proof.
-/
theorem density_properties : Integrable (P.density hκ) ∧
    (∀ x, 0 ≤ P.density hκ x) ∧ HasCompactSupport (P.density hκ) ∧
    groundParameter ((P.speedData hκ).density_integrable hκ) ((P.speedData hκ).density_nonneg hκ)=κ :=
  ⟨(P.speedData hκ).density_integrable hκ,(P.speedData hκ).density_nonneg hκ,
    (P.speedData hκ).density_compact_support κ,(P.speedData hκ).groundParameter_density hκ⟩

end
end chebyshev2.Comparison.Profile
