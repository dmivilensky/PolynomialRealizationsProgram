import «2610.05164v2».Calibration.CubicRoot
import Mathlib.Topology.Order.Compact

/-!
Article: 2610.05164v2, Proposition 5.
Definition 4.
Use: `«2610.05164v2».Calibration.Data.Gamma_two` feeds
`«2610.05164v2».Calibration.ReferenceData.calibration_Gamma_reflection` (calibration Gamma
reflection).
Proof chain: `«2610.05164v2».Calibration.ReferenceData.calibration_constant_normalized` —
2610.05164v2, Theorem 3.2; Constructed contact potential and calibrated reference.
-/
namespace «2610.05164v2».Calibration
noncomputable section
open Set
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/--
Calibration parameters and a continuous reference profile bounded between zero and 2-h. The
sign and domain bounds supply the hypotheses of contact minimization.

Use: `«2610.05164v2».DualCertificate.NormalizedCalibration.S_actual` uses this record of data
and proof obligations to establish the identity `N.S hκ=∫ x,(«2610.05164v2».Filters.linear
((N.calibration.comparisonSpeed hκ).density_integrable hκ) ((N.calibration.comparisonSpeed
hκ).density_nonneg hκ) x)^2`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.
-/
structure Data where
  /-- Positive scale of the calibrated determinant observation. -/
  sigma : ℝ
  /-- Positivity required by the contact/root constructions at this scale. -/
  sigma_positive : 0 < sigma
  /-- Positive base/reference energy parameter. -/
  b : ℝ
  /-- Positivity needed for the calibrated positive cubic root. -/
  b_positive : 0 < b
  /-- Nonnegative observation multiplier. -/
  omega : ℝ
  /-- Sign condition used by contact minimization and the integrated comparison. -/
  omega_nonneg : 0 ≤ omega
  /-- Reference profile on [0,2]. -/
  g : ℝ → ℝ
  /-- Continuity of the reference profile on its entire compact domain. -/
  continuous : ContinuousOn g (Icc 0 2)
  /-- The reference profile lies between zero and 2-h; this controls the contact coefficients and endpoint behavior. -/
  bounds : ∀ h ∈ Icc (0:ℝ) 2, 0 ≤ g h ∧ g h ≤ 2-h

namespace Data
variable (C : Data)

/--
Defines `potential` of type `ℝ` by `C.g (max 0 (min 2 h))`.

Use: `«2610.05164v2».Calibration.Data.F` uses this definition in the displayed construction of
`F`. Its inputs and component formulas are fixed by that definition.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.
-/
def potential (h : ℝ) : ℝ := C.g (max 0 (min 2 h))

/--
Membership in the specified domain/enclosure: `max 0 (min 2 h) ∈ Icc (0:ℝ) 2`.

Use: `«2610.05164v2».Calibration.Data.potential_continuous` uses this assertion to establish
continuity of the displayed function: `Continuous C.potential`.

Article: 2610.05164v2, Theorem E.1 via
`«2610.05164v2».DualCertificate.Data.packed_value_tendsto`.

Proof: The displayed proof term instantiates the cited result with exactly the parameters and
hypotheses of this assertion.
-/
theorem clamp_mem (h : ℝ) : max 0 (min 2 h) ∈ Icc (0:ℝ) 2 :=
  ⟨le_max_left _ _,max_le (by norm_num) (min_le_left _ _)⟩

/--
Continuity of the displayed function: `Continuous C.potential`.

Use: `«2610.05164v2».Calibration.Data.F_continuous` uses this continuity result to establish
continuity of the displayed function: `Continuous (fun p : ℝ × ℝ => C.F p.1 p.2)`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates `«2610.05164v2».Calibration.Data.clamp_mem` with the
arguments shown in the proof.
-/
theorem potential_continuous : Continuous C.potential :=
  C.continuous.comp_continuous (continuous_const.max (continuous_const.min continuous_id)) clamp_mem

/--
Exact identity `C.potential h=C.g h`.

Use: `«2610.05164v2».Calibration.Data.F_diagonal_le` rewrites with this identity to establish
the stated quantitative bound `C.F q q ≤ (2-q)^2`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem potential_eq {h : ℝ} (hh : h ∈ Icc (0:ℝ) 2) : C.potential h=C.g h := by simp only [potential,min_eq_right hh.2,max_eq_right hh.1]

/--
The stated quantitative bound `0 ≤ C.potential h`.

Use: `«2610.05164v2».Calibration.Data.F_zero_le` uses this bound to establish the stated
quantitative bound `C.F q 0 ≤ q^2`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates `«2610.05164v2».Calibration.Data.clamp_mem` with the
arguments shown in the proof.
-/
theorem potential_nonneg (h : ℝ) : 0 ≤ C.potential h := (C.bounds _ (clamp_mem h)).1

/--
The stated quantitative bound `0 < 2+C.sigma*C.potential h`.

Use: `«2610.05164v2».Calibration.Data.F_continuous` uses this bound to establish continuity of
the displayed function: `Continuous (fun p : ℝ × ℝ => C.F p.1 p.2)`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates `«2610.05164v2».Calibration.Data.potential_nonneg` with the
arguments shown in the proof.
-/
theorem denominator_positive (h : ℝ) : 0 < 2+C.sigma*C.potential h := by
  have := C.potential_nonneg h
  have := C.sigma_positive
  positivity

/--
Defines `F` of type `ℝ` by `(2*(q-h)^2-(q^2-2*h)*C.potential h)/(2+C.sigma*C.potential h)`.

Use: `«2610.05164v2».Calibration.Data.F_continuous` uses this definition to establish
continuity of the displayed function: `Continuous (fun p : ℝ × ℝ => C.F p.1 p.2)`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.
-/
def F (q h : ℝ) : ℝ :=
  (2*(q-h)^2-(q^2-2*h)*C.potential h)/(2+C.sigma*C.potential h)

/--
Defines `Gamma` of type `ℝ` by `sInf ((fun u => C.F q (q*u)) '' Icc 0 1)`.

Use: `«2610.05164v2».Calibration.Data.Gamma_continuous` uses this definition to establish
continuity of the displayed function: `Continuous C.Gamma`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.
-/
def Gamma (q : ℝ) : ℝ := sInf ((fun u => C.F q (q*u)) '' Icc 0 1)

/--
Continuity of the displayed function: `Continuous (fun p : ℝ × ℝ => C.F p.1 p.2)`.

Use: `«2610.05164v2».Calibration.Data.F_continuous_right` uses this continuity result to
establish continuity of the displayed function: `Continuous (C.F q)`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates `«2610.05164v2».Calibration.Data.potential_continuous`,
`«2610.05164v2».Calibration.Data.denominator_positive` with the arguments shown in the proof.
-/
theorem F_continuous : Continuous (fun p : ℝ × ℝ => C.F p.1 p.2) := by
  -- Use the identities/estimates `«2610.05164v2».Calibration.Data.potential_continuous`,
  -- `«2610.05164v2».Calibration.Data.denominator_positive` with the arguments shown in the
  -- proof.
  unfold F
  -- Establish continuity hg before using the function at limits or in calculus arguments.
  have hg : Continuous (fun p : ℝ × ℝ => C.potential p.2) := C.potential_continuous.comp continuous_snd
  apply Continuous.div
  · exact (continuous_const.mul ((continuous_fst.sub continuous_snd).pow 2)).sub
      (((continuous_fst.pow 2).sub (continuous_const.mul continuous_snd)).mul hg)
  · exact continuous_const.add (continuous_const.mul hg)
  · intro p
    exact ne_of_gt (C.denominator_positive p.2)

/--
Continuity of the displayed function: `Continuous (C.F q)`.

Use: `«2610.05164v2».Calibration.Data.Gamma_attained` uses this continuity result to establish
constructs witnesses with the exact properties `∃ u ∈ Icc (0:ℝ) 1, C.F q (q*u)=C.Gamma q`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates `«2610.05164v2».Calibration.Data.F_continuous` with the
arguments shown in the proof.
-/
theorem F_continuous_right (q : ℝ) : Continuous (C.F q) :=
  C.F_continuous.comp (continuous_const.prodMk continuous_id)

/--
Continuity of the displayed function: `Continuous C.Gamma`.

Use: `«2610.05164v2».Calibration.Data.Gamma_integrable` uses this continuity result to
establish integrability of the displayed function: `Integrable (fun x => C.Gamma (G.q x))`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates `«2610.05164v2».Calibration.Data.F_continuous` with the
arguments shown in the proof.
-/
theorem Gamma_continuous : Continuous C.Gamma := by
  apply isCompact_Icc.continuous_sInf
  exact C.F_continuous.comp (continuous_fst.prodMk (continuous_fst.mul continuous_snd))

/--
Constructs witnesses with the exact properties `∃ u ∈ Icc (0:ℝ) 1, C.F q (q*u)=C.Gamma q`.

Use: `«2610.05164v2».Calibration.Data.Gamma_nonneg` uses this identity to establish the stated
quantitative bound `0 ≤ C.Gamma q`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates `«2610.05164v2».Calibration.Data.F_continuous_right` with
the arguments shown in the proof.
-/
theorem Gamma_attained (q : ℝ) : ∃ u ∈ Icc (0:ℝ) 1, C.F q (q*u)=C.Gamma q := by
  have hf : Continuous (fun u => C.F q (q*u)) :=
    (C.F_continuous_right q).comp (continuous_const.mul continuous_id)
  have hi := (isCompact_Icc : IsCompact (Icc (0:ℝ) 1)).image hf
  have hne : ((fun u => C.F q (q*u)) '' Icc (0:ℝ) 1).Nonempty :=
    ⟨C.F q (q*0),⟨0,by norm_num,rfl⟩⟩
  exact hi.sInf_mem hne

/--
The stated quantitative bound `C.Gamma q ≤ C.F q (q*u)`.

Use: `«2610.05164v2».Calibration.Data.Gamma_bounds` uses this bound to establish the stated
quantitative bound `0 ≤ C.Gamma q ∧ C.Gamma q ≤ min (q^2) ((2-q)^2)`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates `«2610.05164v2».Calibration.Data.F_continuous_right` with
the arguments shown in the proof.
-/
theorem Gamma_le (q : ℝ) {u : ℝ} (hu : u ∈ Icc (0:ℝ) 1) :
    C.Gamma q ≤ C.F q (q*u) := by
  apply csInf_le _ (mem_image_of_mem _ hu)
  exact (isCompact_Icc.image ((C.F_continuous_right q).comp
    (continuous_const.mul continuous_id))).bddBelow

/--
The stated quantitative bound `C.Gamma q ≤ C.F q h`.

Use: `«2610.05164v2».Calibration.Data.T_nonneg` uses this bound to establish the stated
quantitative bound `0 ≤ C.T (G.q x) (C.calibrationState G x)`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates `«2610.05164v2».Calibration.Data.Gamma_le` with the
arguments shown in the proof.
-/
theorem Gamma_le_state {q h : ℝ} (hq : 0 ≤ q) (hh : h ∈ Icc 0 q) :
    C.Gamma q ≤ C.F q h := by
  rcases eq_or_lt_of_le hq with h0 | hq
  · have hh0 : h=0 := by linarith [hh.1,hh.2]
    simpa [← h0,hh0] using C.Gamma_le 0 (u := 0) (by norm_num)
  · have hu : h/q ∈ Icc (0:ℝ) 1 :=
      ⟨div_nonneg hh.1 hq.le,(div_le_one hq).2 hh.2⟩
    simpa [mul_div_cancel₀ _ (ne_of_gt hq)] using C.Gamma_le q hu

/--
The stated quantitative bound `0 ≤ C.F q h`.

Use: `«2610.05164v2».Calibration.Data.Gamma_nonneg` uses this bound to establish the stated
quantitative bound `0 ≤ C.Gamma q`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.

Proof: Separate `q^2 ≤ 2*h` from its negation; prove the goal under each of these mutually
exclusive hypotheses.
-/
theorem F_nonneg {q h : ℝ} (hq : q ∈ Icc (0:ℝ) 2) (hh : h ∈ Icc 0 q) :
    0 ≤ C.F q h := by
  -- Separate `q^2 ≤ 2*h` from its negation; prove the goal under each of these mutually
  -- exclusive hypotheses.
  have hh2 : h ∈ Icc (0:ℝ) 2 := ⟨hh.1,hh.2.trans hq.2⟩
  have hg := C.bounds h hh2
  apply div_nonneg _ (C.denominator_positive h).le
  rw [C.potential_eq hh2]
  by_cases hb : q^2 ≤ 2*h
  · have hp := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hb) hg.1
    nlinarith [sq_nonneg (q-h)]
  · have hp := mul_le_mul_of_nonneg_left hg.2 (show 0 ≤ q^2-2*h by linarith)
    have he : 2*(q-h)^2-(q^2-2*h)*(2-h)=h*(2-q)^2 := by ring
    have hn : 0 ≤ h*(2-q)^2 := mul_nonneg hh.1 (sq_nonneg _)
    nlinarith

/--
The stated quantitative bound `0 ≤ C.Gamma q`.

Use: `«2610.05164v2».Calibration.Data.Gamma_bounds` uses this bound to establish the stated
quantitative bound `0 ≤ C.Gamma q ∧ C.Gamma q ≤ min (q^2) ((2-q)^2)`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates `«2610.05164v2».Calibration.Data.Gamma_attained`,
`«2610.05164v2».Calibration.Data.F_nonneg` with the arguments shown in the proof.
-/
theorem Gamma_nonneg {q : ℝ} (hq : q ∈ Icc (0:ℝ) 2) : 0 ≤ C.Gamma q := by
  obtain ⟨u,hu,he⟩ := C.Gamma_attained q
  rw [← he]
  exact C.F_nonneg hq ⟨mul_nonneg hq.1 hu.1,mul_le_of_le_one_right hq.1 hu.2⟩

/--
The stated quantitative bound `C.F q 0 ≤ q^2`.

Use: `«2610.05164v2».Calibration.Data.Gamma_bounds` uses this bound to establish the stated
quantitative bound `0 ≤ C.Gamma q ∧ C.Gamma q ≤ min (q^2) ((2-q)^2)`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates `«2610.05164v2».Calibration.Data.denominator_positive`,
`«2610.05164v2».Calibration.Data.potential_nonneg` with the arguments shown in the proof.
-/
theorem F_zero_le (q : ℝ) : C.F q 0 ≤ q^2 := by
  apply (div_le_iff₀ (C.denominator_positive 0)).2
  have hg := C.potential_nonneg 0
  have hs := C.sigma_positive
  have h1 : 0 ≤ q^2*C.potential 0 := mul_nonneg (sq_nonneg _) hg
  have h2 : 0 ≤ C.sigma*(q^2*C.potential 0) := mul_nonneg hs.le h1
  nlinarith

/--
The stated quantitative bound `C.F q q ≤ (2-q)^2`.

Use: `«2610.05164v2».Calibration.Data.Gamma_bounds` uses this bound to establish the stated
quantitative bound `0 ≤ C.Gamma q ∧ C.Gamma q ≤ min (q^2) ((2-q)^2)`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates `«2610.05164v2».Calibration.Data.denominator_positive`,
`«2610.05164v2».Calibration.Data.potential_eq` with the arguments shown in the proof.
-/
theorem F_diagonal_le {q : ℝ} (hq : q ∈ Icc (0:ℝ) 2) : C.F q q ≤ (2-q)^2 := by
  have hg := C.bounds q hq
  apply (div_le_iff₀ (C.denominator_positive q)).2
  rw [C.potential_eq hq]
  have hprod := mul_le_mul_of_nonneg_left hg.2 (sub_nonneg.mpr hq.2)
  have hs := mul_nonneg C.sigma_positive.le
    (mul_nonneg hg.1 (sq_nonneg (2-q)))
  nlinarith [sq_nonneg (2-q)]

/--
The stated quantitative bound `0 ≤ C.Gamma q ∧ C.Gamma q ≤ min (q^2) ((2-q)^2)`.

Use: `«2610.05164v2».Calibration.Data.Gamma_two` uses this bound to establish the identity
`C.Gamma 2=0`.

Article: 2610.05164v2, Theorem 3.5 via
`«2610.05164v2».Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates `«2610.05164v2».Calibration.Data.Gamma_nonneg`,
`«2610.05164v2».Calibration.Data.Gamma_le`, `«2610.05164v2».Calibration.Data.F_zero_le` with
the arguments shown in the proof.
-/
theorem Gamma_bounds {q : ℝ} (hq : q ∈ Icc (0:ℝ) 2) :
    0 ≤ C.Gamma q ∧ C.Gamma q ≤ min (q^2) ((2-q)^2) := by
  -- Use the identities/estimates `«2610.05164v2».Calibration.Data.Gamma_nonneg`,
  -- `«2610.05164v2».Calibration.Data.Gamma_le`, `«2610.05164v2».Calibration.Data.F_zero_le`
  -- with the arguments shown in the proof.
  refine ⟨C.Gamma_nonneg hq,le_min ?_ ?_⟩
  · have h := C.Gamma_le q (u := 0) (by norm_num)
    simp only [mul_zero] at h
    exact h.trans (C.F_zero_le q)
  · have h := C.Gamma_le q (u := 1) (by norm_num)
    simp only [mul_one] at h
    exact h.trans (C.F_diagonal_le hq)

/--
Exact identity `C.Gamma 0=0`.

Use: `«2610.05164v2».Calibration.Data.amplitude_equation` rewrites with this identity to
establish exact identity `κ*(C.amplitude κ q)^3-3*Q q*C.amplitude κ q-C.constant κ q=0`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates `«2610.05164v2».Calibration.Data.Gamma_bounds` with the
arguments shown in the proof.
-/
theorem Gamma_zero : C.Gamma 0=0 := by
  have h := C.Gamma_bounds (q := 0) (by norm_num)
  norm_num at h
  linarith

/--
Exact identity `C.Gamma 2=0`.

Use: `«2610.05164v2».Calibration.Data.amplitude_equation` rewrites with this identity to
establish exact identity `κ*(C.amplitude κ q)^3-3*Q q*C.amplitude κ q-C.constant κ q=0`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates `«2610.05164v2».Calibration.Data.Gamma_bounds` with the
arguments shown in the proof.
-/
theorem Gamma_two : C.Gamma 2=0 := by
  have h := C.Gamma_bounds (q := 2) (by norm_num)
  norm_num at h
  linarith

end Data
end
end «2610.05164v2».Calibration
