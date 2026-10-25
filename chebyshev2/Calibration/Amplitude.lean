import chebyshev2.Calibration.Definition

/-!
Article: chebyshev2, Proposition 8.
Proposition 4: the comparison amplitude, its unique positive root, joint continuity up to the
endpoints, and strict speed estimate.
Use: `chebyshev2.Calibration.Data.Q_div_speed_amplitude` feeds
`chebyshev2.Calibration.Data.Q_div_speed_le_amplitude` (Q div speed le amplitude).
Proof chain: `chebyshev2.Calibration.Data.energy_ge_spectral_bound` — chebyshev2, Theorem 3.5;
Pointwise cubic-conjugate criterion, gauge invariance and regular price.
-/
namespace chebyshev2.Calibration
noncomputable section
open Set Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false

namespace Data
variable (C : Data)

/--
Defines `constant` of type `ℝ` by `2*C.b*Q q+2*κ*C.omega*C.Gamma q`.

Use: `chebyshev2.Calibration.Data.Q_div_speed_amplitude` uses this definition to establish
the stated quantitative bound `Q q/(C.speed κ q*C.amplitude κ q) ≤ 1/(2*C.b)`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.
-/
def constant (κ q : ℝ) : ℝ := 2*C.b*Q q+2*κ*C.omega*C.Gamma q
/--
Defines `amplitude` of type `ℝ` by `if q ∈ Ioo (0:ℝ) 2 then positiveRoot κ (Q q) (C.constant κ
q) else 0`.

Use: `chebyshev2.Calibration.Data.amplitude_unique` rewrites with this definition to
establish exact identity `C.amplitude κ q=v`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.
-/
def amplitude (κ q : ℝ) : ℝ :=
  if q ∈ Ioo (0:ℝ) 2 then positiveRoot κ (Q q) (C.constant κ q) else 0
/--
Defines `speed` of type `ℝ` by `κ*(C.amplitude κ q)^2-Q q`.

Use: `chebyshev2.Calibration.Data.speed_gt_two_Q` uses this definition to establish the
stated quantitative bound `2*Q q < C.speed κ q`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.
-/
def speed (κ q : ℝ) : ℝ := κ*(C.amplitude κ q)^2-Q q

/--
The stated quantitative bound `0 < C.constant κ q`.

Use: `chebyshev2.Calibration.Data.amplitude_continuousOn` uses this bound to establish
continuity on the stated domain: `ContinuousOn (fun p : ℝ × ℝ => C.amplitude p.1 p.2) {p | 0 <
p.1 ∧ p.2 ∈ Icc (0:ℝ) 2}`.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates `chebyshev2.Calibration.Q_positive`,
`chebyshev2.Calibration.Data.Gamma_nonneg` with the arguments shown in the proof.
-/
theorem constant_positive {κ q : ℝ} (hκ : 0 < κ) (hq : q ∈ Ioo (0:ℝ) 2) :
    0 < C.constant κ q := by
  have hQ := Q_positive hq
  have hG := C.Gamma_nonneg ⟨hq.1.le,hq.2.le⟩
  have hb := C.b_positive
  have hw := C.omega_nonneg
  unfold constant
  positivity

/--
Exact identity `0 < C.amplitude κ q ∧ κ*(C.amplitude κ q)^3-3*Q q*C.amplitude κ q-C.constant κ
q=0`.

Use: `chebyshev2.Calibration.Data.Q_div_speed_amplitude` uses this identity to establish
the stated quantitative bound `Q q/(C.speed κ q*C.amplitude κ q) ≤ 1/(2*C.b)`.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates `chebyshev2.Calibration.positiveRoot_spec`,
`chebyshev2.Calibration.Q_positive`, `chebyshev2.Calibration.Data.constant_positive`
with the arguments shown in the proof.
-/
theorem amplitude_spec {κ q : ℝ} (hκ : 0 < κ) (hq : q ∈ Ioo (0:ℝ) 2) :
    0 < C.amplitude κ q ∧
      κ*(C.amplitude κ q)^3-3*Q q*C.amplitude κ q-C.constant κ q=0 := by
  rw [amplitude,ite_eq_left hq]
  exact positiveRoot_spec hκ (Q_positive hq).le (C.constant_positive hκ hq)

/--
Exact identity `C.amplitude κ 0=0`.

Use: `chebyshev2.Calibration.Data.amplitude_equation` rewrites with this identity to
establish exact identity `κ*(C.amplitude κ q)^3-3*Q q*C.amplitude κ q-C.constant κ q=0`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem amplitude_zero (κ : ℝ) : C.amplitude κ 0=0 := by simp [amplitude]
/--
Exact identity `C.amplitude κ 2=0`.

Use: `chebyshev2.Calibration.Data.amplitude_equation` rewrites with this identity to
establish exact identity `κ*(C.amplitude κ q)^3-3*Q q*C.amplitude κ q-C.constant κ q=0`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem amplitude_two (κ : ℝ) : C.amplitude κ 2=0 := by simp [amplitude]

/--
The stated quantitative bound `0 ≤ C.amplitude κ q`.

Use: `chebyshev2.Calibration.Data.amplitude_continuousOn` uses this bound to establish
continuity on the stated domain: `ContinuousOn (fun p : ℝ × ℝ => C.amplitude p.1 p.2) {p | 0 <
p.1 ∧ p.2 ∈ Icc (0:ℝ) 2}`.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.

Proof: Separate `q ∈ Ioo (0:ℝ) 2` from its negation; prove the goal under each of these
mutually exclusive hypotheses.
-/
theorem amplitude_nonneg {κ : ℝ} (hκ : 0 < κ) (q : ℝ) : 0 ≤ C.amplitude κ q := by
  by_cases hq : q ∈ Ioo (0:ℝ) 2
  · exact (C.amplitude_spec hκ hq).1.le
  · simp [amplitude,hq]

/--
Exact identity `q=0 ∨ q=2`.

Use: `chebyshev2.Calibration.Data.amplitude_equation` uses this identity to establish exact
identity `κ*(C.amplitude κ q)^3-3*Q q*C.amplitude κ q-C.constant κ q=0`.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.

Proof: Separate `q=0` from its negation; prove the goal under each of these mutually exclusive
hypotheses.
-/
theorem endpoint_cases {q : ℝ} (hq : q ∈ Icc (0:ℝ) 2) (hi : q ∉ Ioo (0:ℝ) 2) :
    q=0 ∨ q=2 := by
  by_cases h : q=0
  · exact Or.inl h
  · exact Or.inr (le_antisymm hq.2 (not_lt.mp (fun hc => hi ⟨lt_of_le_of_ne hq.1 (Ne.symm h),hc⟩)))

/--
Exact identity `κ*(C.amplitude κ q)^3-3*Q q*C.amplitude κ q-C.constant κ q=0`.

Use: `chebyshev2.Calibration.Data.speed_amplitude` uses this identity to establish exact
identity `C.speed κ q*C.amplitude κ q=2*Q q*C.amplitude κ q+C.constant κ q`.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.

Proof: Separate `q ∈ Ioo (0:ℝ) 2` from its negation; prove the goal under each of these
mutually exclusive hypotheses.
-/
theorem amplitude_equation {κ q : ℝ} (hκ : 0 < κ) (hq : q ∈ Icc (0:ℝ) 2) :
    κ*(C.amplitude κ q)^3-3*Q q*C.amplitude κ q-C.constant κ q=0 := by
  by_cases hi : q ∈ Ioo (0:ℝ) 2
  · exact (C.amplitude_spec hκ hi).2
  · rcases endpoint_cases hq hi with rfl | rfl <;>
      simp [C.amplitude_zero,C.amplitude_two,constant,Q,C.Gamma_zero,C.Gamma_two]

/--
Exact identity `C.amplitude κ q=v`.

Use: `chebyshev2.Calibration.Data.amplitude_reflection` uses this identity to establish
exact identity `C.amplitude κ (2-q)=C.amplitude κ q`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates `chebyshev2.Calibration.positiveRoot_eq`,
`chebyshev2.Calibration.Q_positive`, `chebyshev2.Calibration.Data.constant_positive`
with the arguments shown in the proof.
-/
theorem amplitude_unique {κ q v : ℝ} (hκ : 0 < κ) (hq : q ∈ Ioo (0:ℝ) 2)
    (hv : 0 < v) (he : κ*v^3-3*Q q*v-C.constant κ q=0) : C.amplitude κ q=v := by
  rw [amplitude,ite_eq_left hq]
  exact positiveRoot_eq hκ (Q_positive hq).le (C.constant_positive hκ hq) hv he

/--
The stated quantitative bound `0 < cubic κ (Q q) (C.constant κ q) x`.

Use: `chebyshev2.Calibration.Data.amplitude_continuousOn` uses this bound to establish
continuity on the stated domain: `ContinuousOn (fun p : ℝ × ℝ => C.amplitude p.1 p.2) {p | 0 <
p.1 ∧ p.2 ∈ Icc (0:ℝ) 2}`.

Article: chebyshev2, Theorem E.1 via
`chebyshev2.DualCertificate.Data.packed_value_tendsto`.

Proof: Separate `q ∈ Ioo (0:ℝ) 2` from its negation; prove the goal under each of these
mutually exclusive hypotheses.
-/
theorem amplitude_poly_pos {κ q x : ℝ} (hκ : 0 < κ) (hq : q ∈ Icc (0:ℝ) 2)
    (hx : C.amplitude κ q < x) : 0 < cubic κ (Q q) (C.constant κ q) x := by
  -- Separate `q ∈ Ioo (0:ℝ) 2` from its negation; prove the goal under each of these mutually
  -- exclusive hypotheses.
  by_cases hi : q ∈ Ioo (0:ℝ) 2
  · apply (cubic_pos_iff hκ (Q_positive hi).le (C.constant_positive hκ hi)
      ((C.amplitude_nonneg hκ q).trans hx.le)).2
    simpa [amplitude,hi] using hx
  · rcases endpoint_cases hq hi with rfl | rfl
    · simp only [C.amplitude_zero] at hx
      simpa [cubic,constant,Q,C.Gamma_zero] using mul_pos hκ (pow_pos hx 3)
    · simp only [C.amplitude_two] at hx
      simpa [cubic,constant,Q,C.Gamma_two] using mul_pos hκ (pow_pos hx 3)

/--
The stated quantitative bound `C.amplitude κ q < x`.

Use: `chebyshev2.Calibration.Data.amplitude_continuousOn` uses this bound to establish
continuity on the stated domain: `ContinuousOn (fun p : ℝ × ℝ => C.amplitude p.1 p.2) {p | 0 <
p.1 ∧ p.2 ∈ Icc (0:ℝ) 2}`.

Article: chebyshev2, Theorem E.1 via
`chebyshev2.DualCertificate.Data.packed_value_tendsto`.

Proof: Separate `q ∈ Ioo (0:ℝ) 2` from its negation; prove the goal under each of these
mutually exclusive hypotheses.
-/
theorem amplitude_lt_of_poly_pos {κ q x : ℝ} (hκ : 0 < κ) (_hq : q ∈ Icc (0:ℝ) 2)
    (hx : 0 < x) (hp : 0 < cubic κ (Q q) (C.constant κ q) x) : C.amplitude κ q < x := by
  by_cases hi : q ∈ Ioo (0:ℝ) 2
  · simpa [amplitude,hi] using
      (cubic_pos_iff hκ (Q_positive hi).le (C.constant_positive hκ hi) hx.le).1 hp
  · simp [amplitude,hi,hx]

/--
Continuity on the stated domain: `ContinuousOn (fun p : ℝ × ℝ => C.amplitude p.1 p.2) {p | 0 <
p.1 ∧ p.2 ∈ Icc (0:ℝ) 2}`.

Use: `chebyshev2.Calibration.Data.amplitudeIntegral_continuousOn` uses this continuity
result to establish continuity on the stated domain: `ContinuousOn (fun κ => ∫ q in (0:ℝ)..2,
C.amplitude κ q) (Ioi (0:ℝ))`.

Article: chebyshev2, Theorem E.1 via
`chebyshev2.DualCertificate.Data.packed_value_tendsto`.

Proof: Separate `a < 0` from its negation; prove the goal under each of these mutually
exclusive hypotheses. Assume the failure of the desired conclusion and derive a contradiction
from the available bounds/identities. Intersect the eventual or almost-everywhere hypotheses,
then prove the asserted relation at an arbitrary point in that intersection.
-/
theorem amplitude_continuousOn : ContinuousOn (fun p : ℝ × ℝ => C.amplitude p.1 p.2)
    {p | 0 < p.1 ∧ p.2 ∈ Icc (0:ℝ) 2} := by
  -- Establish continuity hp before using the function at limits or in calculus arguments.
  have hp (x : ℝ) : Continuous (fun p : ℝ × ℝ => cubic p.1 (Q p.2) (C.constant p.1 p.2) x) := by
    -- Establish continuity hg before using the function at limits or in calculus arguments.
    have hg : Continuous (fun p : ℝ × ℝ => C.Gamma p.2) := C.Gamma_continuous.comp continuous_snd
    unfold cubic constant Q
    fun_prop
  intro p h
  apply tendsto_order.2
  constructor
  · intro a ha
    by_cases ha0 : a < 0
    · filter_upwards [self_mem_nhdsWithin] with p' hp'
      exact ha0.trans_le (C.amplitude_nonneg hp'.1 _)
    · have ha0 := not_lt.mp ha0
      have hi : p.2 ∈ Ioo (0:ℝ) 2 := by
        by_contra hi
        simp [amplitude,hi] at ha
        linarith
      have hn : cubic p.1 (Q p.2) (C.constant p.1 p.2) a < 0 := by
        apply (cubic_neg_iff h.1 (Q_positive hi).le (C.constant_positive h.1 hi) ha0).2
        simpa [amplitude,hi] using ha
      have he := (hp a).continuousAt.eventually (gt_mem_nhds hn)
      have hnear : ∀ᶠ p' : ℝ × ℝ in 𝓝 p, p'.2 ∈ Ioo (0:ℝ) 2 :=
        continuous_snd.continuousAt.preimage_mem_nhds (isOpen_Ioo.mem_nhds hi)
      filter_upwards [he.filter_mono nhdsWithin_le_nhds,hnear.filter_mono nhdsWithin_le_nhds,
        self_mem_nhdsWithin] with p' he hi' hp'
      simpa [amplitude,hi'] using
        (cubic_neg_iff hp'.1 (Q_positive hi').le (C.constant_positive hp'.1 hi') ha0).1 he
  · intro a ha
    have ha0 : 0 < a := (C.amplitude_nonneg h.1 _).trans_lt ha
    have hn := C.amplitude_poly_pos h.1 h.2 ha
    have he := (hp a).continuousAt.eventually (lt_mem_nhds hn)
    filter_upwards [he.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with p' he hp'
    exact C.amplitude_lt_of_poly_pos hp'.1 hp'.2 ha0 he

/--
The stated quantitative bound `2*Q q < C.speed κ q`.

Use: `chebyshev2.Calibration.Data.speed_gt_two_thirds` uses this bound to establish the
stated quantitative bound `2/3*κ*(C.amplitude κ q)^2 < C.speed κ q`.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates `chebyshev2.Calibration.Data.amplitude_spec`,
`chebyshev2.Calibration.Data.constant_positive` with the arguments shown in the proof.
-/
theorem speed_gt_two_Q {κ q : ℝ} (hκ : 0 < κ) (hq : q ∈ Ioo (0:ℝ) 2) :
    2*Q q < C.speed κ q := by
  obtain ⟨hv,he⟩ := C.amplitude_spec hκ hq
  have hc := C.constant_positive hκ hq
  unfold speed
  nlinarith

/--
The stated quantitative bound `0 < C.speed κ q`.

Use: `chebyshev2.Calibration.Data.Q_div_speed_amplitude` uses this bound to establish the
stated quantitative bound `Q q/(C.speed κ q*C.amplitude κ q) ≤ 1/(2*C.b)`.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates `chebyshev2.Calibration.Q_positive`,
`chebyshev2.Calibration.Data.speed_gt_two_Q` with the arguments shown in the proof.
-/
theorem speed_positive {κ q : ℝ} (hκ : 0 < κ) (hq : q ∈ Ioo (0:ℝ) 2) :
    0 < C.speed κ q := (by linarith [Q_positive hq] : 0 < 2*Q q).trans (C.speed_gt_two_Q hκ hq)

/--
Exact identity `C.speed κ q*C.amplitude κ q=2*Q q*C.amplitude κ q+C.constant κ q`.

Use: `chebyshev2.Calibration.Data.Q_div_speed_amplitude` rewrites with this identity to
establish the stated quantitative bound `Q q/(C.speed κ q*C.amplitude κ q) ≤ 1/(2*C.b)`.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates `chebyshev2.Calibration.Data.amplitude_equation` with
the arguments shown in the proof.
-/
theorem speed_amplitude {κ q : ℝ} (hκ : 0 < κ) (hq : q ∈ Icc (0:ℝ) 2) :
    C.speed κ q*C.amplitude κ q=2*Q q*C.amplitude κ q+C.constant κ q := by
  have he := C.amplitude_equation hκ hq
  unfold speed
  nlinarith

/--
The stated quantitative bound `2/3*κ*(C.amplitude κ q)^2 < C.speed κ q`.

Use: `chebyshev2.Calibration.Data.amplitude_square_div_speed` uses this bound to establish
the stated quantitative bound `(C.amplitude κ q)^2/C.speed κ q < 3/(2*κ)`.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates `chebyshev2.Calibration.Data.speed_gt_two_Q` with the
arguments shown in the proof.
-/
theorem speed_gt_two_thirds {κ q : ℝ} (hκ : 0 < κ) (hq : q ∈ Ioo (0:ℝ) 2) :
    2/3*κ*(C.amplitude κ q)^2 < C.speed κ q := by
  have h := C.speed_gt_two_Q hκ hq
  unfold speed at *
  linarith

/--
The stated quantitative bound `(C.amplitude κ q)^2/C.speed κ q < 3/(2*κ)`.

Use: `chebyshev2.Calibration.Data.amplitudeRatio_L1_tendsto` uses this bound to establish
convergence along the specified source filter to the specified limit: `Tendsto (fun κ => ∫ q in
Ioo (0:ℝ) 2, |C.amplitudeRatio κ q-C.amplitudeRatio k q|) (𝓝 k) (𝓝 0)`.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates `chebyshev2.Calibration.Data.speed_positive`,
`chebyshev2.Calibration.Data.speed_gt_two_thirds` with the arguments shown in the proof.
-/
theorem amplitude_square_div_speed {κ q : ℝ} (hκ : 0 < κ) (hq : q ∈ Ioo (0:ℝ) 2) :
    (C.amplitude κ q)^2/C.speed κ q < 3/(2*κ) := by
  apply (div_lt_div_iff₀ (C.speed_positive hκ hq) (by positivity : 0 < 2*κ)).2
  linarith [C.speed_gt_two_thirds hκ hq]

/--
The stated quantitative bound `Q q/(C.speed κ q*C.amplitude κ q) ≤ 1/(2*C.b)`.

Use: `chebyshev2.Calibration.Data.Q_div_speed_le_amplitude` uses this bound to establish
the stated quantitative bound `chebyshev2.Calibration.Q q/C.speed κ q ≤ C.amplitude κ
q/(2*C.b)`.

Article: chebyshev2, Theorem 3.5 via
`chebyshev2.Calibration.Data.energy_ge_spectral_bound`.

Proof: Use the identities/estimates `chebyshev2.Calibration.Data.amplitude_spec`,
`chebyshev2.Calibration.Data.speed_positive`,
`chebyshev2.Calibration.Data.speed_amplitude` with the arguments shown in the proof.
-/
theorem Q_div_speed_amplitude {κ q : ℝ} (hκ : 0 < κ) (hq : q ∈ Ioo (0:ℝ) 2) :
    Q q/(C.speed κ q*C.amplitude κ q) ≤ 1/(2*C.b) := by
  -- Use the identities/estimates `chebyshev2.Calibration.Data.amplitude_spec`,
  -- `chebyshev2.Calibration.Data.speed_positive`,
  -- `chebyshev2.Calibration.Data.speed_amplitude` with the arguments shown in the proof.
  have hv := (C.amplitude_spec hκ hq).1
  apply (div_le_div_iff₀ (mul_pos (C.speed_positive hκ hq) hv)
    (by linarith [C.b_positive] : 0 < 2*C.b)).2
  rw [C.speed_amplitude hκ ⟨hq.1.le,hq.2.le⟩]
  have hQ := Q_positive hq
  have hG := C.Gamma_nonneg ⟨hq.1.le,hq.2.le⟩
  have hw := C.omega_nonneg
  unfold constant
  nlinarith [mul_nonneg (mul_nonneg hκ.le hw) hG]

end Data
end
end chebyshev2.Calibration
