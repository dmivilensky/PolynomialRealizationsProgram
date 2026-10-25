import chebyshev2.Calibration.Tangent
import Mathlib.Topology.Order.IntermediateValue

/-!
Article: chebyshev2, Lemma 19.
Positive root of κν³ - 3Qν - c, constructed by the intermediate value theorem.
Use: `chebyshev2.Calibration.positiveRoot_continuousOn` feeds
`chebyshev2.Calibration.positiveRoot_contDiffOn` (positive Root cont Diff On).
Proof chain: `chebyshev2.DualCertificate.Data.admissible_stable` — chebyshev2, Theorem E.1;
Stability of strict admissibility and uniform transfer of the certificate value.
-/
namespace chebyshev2.Calibration
noncomputable section
open Set Filter
open scoped Topology

/--
Defines `cubic` of type `ℝ` by `κ*v^3-3*Q*v-c`.

Use: `chebyshev2.Calibration.positiveRoot_continuousOn` uses this definition to establish
continuity on the stated domain: `ContinuousOn (fun p : ℝ × ℝ × ℝ => positiveRoot p.1 p.2.1
p.2.2) {p | 0 < p.1 ∧ 0 ≤ p.2.1 ∧ 0 < p.2.2}`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.
-/
def cubic (κ Q c v : ℝ) : ℝ := κ*v^3-3*Q*v-c

/--
Constructs witnesses with the exact properties `∃ v : ℝ, 0 < v ∧ cubic κ Q c v=0`.

Use: `chebyshev2.Calibration.positiveRoot_spec` uses this identity to establish exact
identity `0 < positiveRoot κ Q c ∧ cubic κ Q c (positiveRoot κ Q c)=0`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem exists_positive_cubic_root {κ Q c : ℝ}
    (hκ : 0 < κ) (hQ : 0 ≤ Q) (hc : 0 < c) :
    ∃ v : ℝ, 0 < v ∧ cubic κ Q c v=0 := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  let M : ℝ := (3*Q+c)/κ+1
  have hM : 1 ≤ M := by
    have : 0 ≤ (3*Q+c)/κ := by positivity
    dsimp [M]
    linarith
  have he : κ*M=3*Q+c+κ := by dsimp [M]; field_simp
  have h1 : 0 ≤ κ*M*(M-1) := by positivity
  have h2 : 0 ≤ c*(M-1) := by positivity
  have h3 : 0 ≤ (κ*M^2-3*Q-c)*M := by
    apply mul_nonneg _ (by linarith)
    nlinarith
  have hp : 0 ≤ cubic κ Q c M := by dsimp [cubic]; nlinarith
  have hz : cubic κ Q c 0 ≤ 0 := by simp [cubic,hc.le]
  -- Establish continuity hcont before using the function at limits or in calculus arguments.
  have hcont : Continuous (cubic κ Q c) := by unfold cubic; fun_prop
  obtain ⟨v,hv,heq⟩ := intermediate_value_Icc (by linarith : 0 ≤ M) hcont.continuousOn ⟨hz,hp⟩
  refine ⟨v,?_,heq⟩
  apply lt_of_le_of_ne hv.1
  intro hv0
  rw [← hv0] at heq
  simp [cubic,ne_of_gt hc] at heq

/--
The quotient form yields a strictly positive factor on the whole nonnegative axis, even below
the local maximum of the cubic.

Exact identity `cubic κ Q c x=(x-v)*(κ*(x^2+x*v)+c/v)`.

Use: `chebyshev2.Calibration.cubic_neg_iff` rewrites with this identity to establish
equivalence of the displayed criteria: `cubic κ Q c x < 0 ↔ x < positiveRoot κ Q c`.

Article: chebyshev2, Theorem E.1 via
`chebyshev2.DualCertificate.Data.packed_value_tendsto`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem cubic_factor {κ Q c v : ℝ} (hv : 0 < v) (he : cubic κ Q c v=0) (x : ℝ) :
    cubic κ Q c x=(x-v)*(κ*(x^2+x*v)+c/v) := by
  dsimp [cubic] at *
  field_simp
  linear_combination x*he

/--
The stated quantitative bound `0 < κ*(x^2+x*v)+c/v`.

Use: `chebyshev2.Calibration.cubic_neg_iff` uses this bound to establish equivalence of the
displayed criteria: `cubic κ Q c x < 0 ↔ x < positiveRoot κ Q c`.

Article: chebyshev2, Theorem E.1 via
`chebyshev2.DualCertificate.Data.packed_value_tendsto`.

Proof: The tactic block explicitly constructs the required witness or reduces the goal to the
local facts stated below.
-/
theorem cubic_factor_positive {κ c v x : ℝ}
    (hκ : 0 < κ) (hc : 0 < c) (hv : 0 < v) (hx : 0 ≤ x) :
    0 < κ*(x^2+x*v)+c/v := by positivity

/--
Exact identity `u=v`.

Use: `chebyshev2.Calibration.positiveRoot_eq` uses this identity to establish exact
identity `positiveRoot κ Q c=v`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates `chebyshev2.Calibration.cubic_factor_positive`,
`chebyshev2.Calibration.cubic_factor` with the arguments shown in the proof.
-/
theorem positive_cubic_root_unique {κ Q c u v : ℝ}
    (hκ : 0 < κ) (hc : 0 < c) (hu : 0 < u) (hv : 0 < v)
    (heu : cubic κ Q c u=0) (hev : cubic κ Q c v=0) : u=v := by
  rw [cubic_factor hu heu] at hev
  have hf := ne_of_gt (cubic_factor_positive hκ hc hu hv.le)
  exact (sub_eq_zero.mp ((mul_eq_zero.mp hev).resolve_right hf)).symm

/--
Defines `positiveRoot` of type `ℝ` by `if h : 0 < κ ∧ 0 ≤ Q ∧ 0 < c then Classical.choose
(exists_positive_cubic_root h.1 h.2.1 h.2.2) else 0`.

Use: `chebyshev2.Calibration.positiveRoot_continuousOn` uses this definition to establish
continuity on the stated domain: `ContinuousOn (fun p : ℝ × ℝ × ℝ => positiveRoot p.1 p.2.1
p.2.2) {p | 0 < p.1 ∧ 0 ≤ p.2.1 ∧ 0 < p.2.2}`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.
-/
def positiveRoot (κ Q c : ℝ) : ℝ :=
  if h : 0 < κ ∧ 0 ≤ Q ∧ 0 < c then
    Classical.choose (exists_positive_cubic_root h.1 h.2.1 h.2.2) else 0

/--
Exact identity `0 < positiveRoot κ Q c ∧ cubic κ Q c (positiveRoot κ Q c)=0`.

Use: `chebyshev2.Calibration.cubic_neg_iff` uses this identity to establish equivalence of
the displayed criteria: `cubic κ Q c x < 0 ↔ x < positiveRoot κ Q c`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates `chebyshev2.Calibration.exists_positive_cubic_root`
with the arguments shown in the proof.
-/
theorem positiveRoot_spec {κ Q c : ℝ} (hκ : 0 < κ) (hQ : 0 ≤ Q) (hc : 0 < c) :
    0 < positiveRoot κ Q c ∧ cubic κ Q c (positiveRoot κ Q c)=0 := by
  rw [positiveRoot,dite_eq_left ⟨hκ,hQ,hc⟩]
  exact Classical.choose_spec (exists_positive_cubic_root hκ hQ hc)

/--
Exact identity `positiveRoot κ Q c=v`.

Use: `chebyshev2.Calibration.Data.amplitude_unique` uses this identity to establish exact
identity `C.amplitude κ q=v`.

Article: chebyshev2, Theorem 3.6 via
`chebyshev2.DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates `chebyshev2.Calibration.positive_cubic_root_unique`,
`chebyshev2.Calibration.positiveRoot_spec` with the arguments shown in the proof.
-/
theorem positiveRoot_eq {κ Q c v : ℝ} (hκ : 0 < κ) (hQ : 0 ≤ Q) (hc : 0 < c)
    (hv : 0 < v) (he : cubic κ Q c v=0) : positiveRoot κ Q c=v :=
  positive_cubic_root_unique hκ hc (positiveRoot_spec hκ hQ hc).1 hv
    (positiveRoot_spec hκ hQ hc).2 he

/--
Equivalence of the displayed criteria: `cubic κ Q c x < 0 ↔ x < positiveRoot κ Q c`.

Use: `chebyshev2.Calibration.positiveRoot_continuousOn` uses this bound to establish
continuity on the stated domain: `ContinuousOn (fun p : ℝ × ℝ × ℝ => positiveRoot p.1 p.2.1
p.2.2) {p | 0 < p.1 ∧ 0 ≤ p.2.1 ∧ 0 < p.2.2}`.

Article: chebyshev2, Theorem E.1 via
`chebyshev2.DualCertificate.Data.packed_value_tendsto`.

Proof: Use the identities/estimates `chebyshev2.Calibration.positiveRoot_spec`,
`chebyshev2.Calibration.cubic_factor`, `chebyshev2.Calibration.cubic_factor_positive`
with the arguments shown in the proof.
-/
theorem cubic_neg_iff {κ Q c x : ℝ} (hκ : 0 < κ) (hQ : 0 ≤ Q) (hc : 0 < c)
    (hx : 0 ≤ x) : cubic κ Q c x < 0 ↔ x < positiveRoot κ Q c := by
  -- Use the identities/estimates `chebyshev2.Calibration.positiveRoot_spec`,
  -- `chebyshev2.Calibration.cubic_factor`,
  -- `chebyshev2.Calibration.cubic_factor_positive` with the arguments shown in the proof.
  obtain ⟨hv,he⟩ := positiveRoot_spec hκ hQ hc
  rw [cubic_factor hv he]
  have hp := cubic_factor_positive hκ hc hv hx
  constructor
  · intro h
    exact sub_neg.mp (neg_of_mul_neg_left h hp.le)
  · intro h
    exact mul_neg_of_neg_of_pos (sub_neg.mpr h) hp

/--
Equivalence of the displayed criteria: `0 < cubic κ Q c x ↔ positiveRoot κ Q c < x`.

Use: `chebyshev2.Calibration.positiveRoot_continuousOn` uses this bound to establish
continuity on the stated domain: `ContinuousOn (fun p : ℝ × ℝ × ℝ => positiveRoot p.1 p.2.1
p.2.2) {p | 0 < p.1 ∧ 0 ≤ p.2.1 ∧ 0 < p.2.2}`.

Article: chebyshev2, Theorem E.1 via
`chebyshev2.DualCertificate.Data.packed_value_tendsto`.

Proof: Use the identities/estimates `chebyshev2.Calibration.positiveRoot_spec`,
`chebyshev2.Calibration.cubic_factor`, `chebyshev2.Calibration.cubic_factor_positive`
with the arguments shown in the proof.
-/
theorem cubic_pos_iff {κ Q c x : ℝ} (hκ : 0 < κ) (hQ : 0 ≤ Q) (hc : 0 < c)
    (hx : 0 ≤ x) : 0 < cubic κ Q c x ↔ positiveRoot κ Q c < x := by
  obtain ⟨hv,he⟩ := positiveRoot_spec hκ hQ hc
  rw [cubic_factor hv he,mul_pos_iff_of_pos_right (cubic_factor_positive hκ hc hv hx),sub_pos]

/--
Continuity in all three coefficients, on their full natural domain.

Continuity on the stated domain: `ContinuousOn (fun p : ℝ × ℝ × ℝ => positiveRoot p.1 p.2.1
p.2.2) {p | 0 < p.1 ∧ 0 ≤ p.2.1 ∧ 0 < p.2.2}`.

Use: `chebyshev2.Calibration.positiveRoot_contDiffOn` uses this continuity result to
establish smoothness to the stated order: `ContDiffOn ℝ ∞ (fun p : ℝ × ℝ × ℝ => positiveRoot
p.1 p.2.1 p.2.2) {p | 0 < p.1 ∧ 0 ≤ p.2.1 ∧ 0 < p.2.2}`.

Article: chebyshev2, Theorem E.1 via `chebyshev2.DualCertificate.Data.admissible_stable`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem positiveRoot_continuousOn : ContinuousOn
    (fun p : ℝ × ℝ × ℝ => positiveRoot p.1 p.2.1 p.2.2)
    {p | 0 < p.1 ∧ 0 ≤ p.2.1 ∧ 0 < p.2.2} := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  intro p hp
  apply tendsto_order.2
  have hv := (positiveRoot_spec hp.1 hp.2.1 hp.2.2).1
  -- Establish continuity hpoly before using the function at limits or in calculus arguments.
  have hpoly (x : ℝ) : Continuous (fun p : ℝ × ℝ × ℝ => cubic p.1 p.2.1 p.2.2 x) := by
    unfold cubic
    fun_prop
  constructor
  · intro a ha
    let x := max a 0
    have hx : 0 ≤ x := le_max_right _ _
    have hxa : a ≤ x := le_max_left _ _
    have hxv : x < positiveRoot p.1 p.2.1 p.2.2 := max_lt ha hv
    have hn := (cubic_neg_iff hp.1 hp.2.1 hp.2.2 hx).2 hxv
    have he := (hpoly x).continuousAt.eventually (gt_mem_nhds hn)
    filter_upwards [he.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with p' he hp'
    exact hxa.trans_lt ((cubic_neg_iff hp'.1 hp'.2.1 hp'.2.2 hx).1 he)
  · intro a ha
    have hx : 0 ≤ a := (hv.trans ha).le
    have hn := (cubic_pos_iff hp.1 hp.2.1 hp.2.2 hx).2 ha
    have he := (hpoly a).continuousAt.eventually (lt_mem_nhds hn)
    filter_upwards [he.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with p' he hp'
    exact (cubic_pos_iff hp'.1 hp'.2.1 hp'.2.2 hx).1 he

end
end chebyshev2.Calibration
