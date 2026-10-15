import «2610.05164v2».Comparison.ProfileGeometry

/-!
Article: 2610.05164v2, Proposition 5.
The variable-b reference amplitude of Theorem 3.2.
Use: `«2610.05164v2».Calibration.ReferenceData.speed_gt_two_Q` feeds
`«2610.05164v2».Calibration.ReferenceData.speed_gt_two_thirds` (speed gt two thirds).
Proof chain: `«2610.05164v2».Calibration.ReferenceData.contact_strictMono` — 2610.05164v2, Theorem
3.2; Constructed contact potential and calibrated reference.
-/
namespace «2610.05164v2».Calibration
noncomputable section
open Set Filter Real
open scoped Topology ContDiff
set_option backward.isDefEq.respectTransparency false

/--
A positive ground parameter and a positive, smooth, monotone reference coefficient on [0,1].
These hypotheses support the cubic reference amplitude and its endpoint regularity.

Use: `«2610.05164v2».Calibration.ReferenceData.amplitude` uses this record of data and proof
obligations in the displayed construction of `amplitude`. Its inputs and component formulas are
fixed by that definition.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.
-/
structure ReferenceData where
  /-- Prescribed positive ground parameter for the reference construction. -/
  k : ℝ
  /-- The parameter is strictly positive, so normalization by k is legitimate. -/
  k_positive : 0 < k
  /-- Smooth reference coefficient in the cubic amplitude equation. -/
  b : ℝ → ℝ
  /-- Smoothness on the full closed coordinate interval. -/
  smooth : ContDiffOn ℝ ∞ b (Icc 0 1)
  /-- Strict positivity of the reference coefficient, including its endpoint values. -/
  positive : ∀ t ∈ Icc (0:ℝ) 1, 0 < b t
  /-- Monotonicity of the reference coefficient on the coordinate interval. -/
  monotone : MonotoneOn b (Icc 0 1)

namespace ReferenceData
variable (R : ReferenceData)

/--
Defines `coefficient` of type `ℝ` by `R.b (max 0 (min 1 t))`.

Use: `«2610.05164v2».Calibration.ReferenceData.coefficient_eq` rewrites with this definition to
establish exact identity `R.coefficient t=R.b t`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.
-/
def coefficient (t : ℝ) : ℝ := R.b (max 0 (min 1 t))

/--
Exact identity `R.coefficient t=R.b t`.

Use: `«2610.05164v2».Calibration.ReferenceData.root_continuousOn` rewrites with this identity
to establish continuity on the stated domain: `ContinuousOn R.root (Icc (0:ℝ) 1)`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem coefficient_eq {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) : R.coefficient t=R.b t := by simp only [coefficient,min_eq_right ht.2,max_eq_right ht.1]

/--
Continuity of the displayed function: `Continuous R.coefficient`.

Use: `«2610.05164v2».Calibration.ReferenceData.root_continuousOn` uses this continuity result
to establish continuity on the stated domain: `ContinuousOn R.root (Icc (0:ℝ) 1)`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: The displayed proof term instantiates the cited result with exactly the parameters and
hypotheses of this assertion.
-/
theorem coefficient_continuous : Continuous R.coefficient :=
  R.smooth.continuousOn.comp_continuous (continuous_const.max (continuous_const.min continuous_id))
    (fun t => ⟨le_max_left _ _,max_le (by norm_num) (min_le_left _ _)⟩)

/--
Defines `root` of type `ℝ` by `if 0 < t then positiveRoot R.k t (2*R.coefficient t*t) else 0`.

Use: `«2610.05164v2».Calibration.ReferenceData.amplitude` uses this definition in the displayed
construction of `amplitude`. Its inputs and component formulas are fixed by that definition.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.
-/
def root (t : ℝ) : ℝ := if 0 < t then positiveRoot R.k t (2*R.coefficient t*t) else 0

/--
Exact identity `0 < R.root t ∧ cubic R.k t (2*R.b t*t) (R.root t)=0`.

Use: `«2610.05164v2».Calibration.ReferenceData.amplitude_positive` uses this identity to
establish the stated quantitative bound `0 < R.amplitude q`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates `«2610.05164v2».Calibration.ReferenceData.coefficient_eq`,
`«2610.05164v2».Calibration.positiveRoot_spec` with the arguments shown in the proof.
-/
theorem root_spec {t : ℝ} (ht : t ∈ Ioc (0:ℝ) 1) :
    0 < R.root t ∧ cubic R.k t (2*R.b t*t) (R.root t)=0 := by
  rw [root,ite_eq_left ht.1,R.coefficient_eq ⟨ht.1.le,ht.2⟩]
  exact positiveRoot_spec R.k_positive ht.1.le (mul_pos (mul_pos (by norm_num) (R.positive t ⟨ht.1.le,ht.2⟩)) ht.1)

/--
Exact identity `R.root 0=0`.

Use: `«2610.05164v2».Calibration.ReferenceData.amplitude_two` rewrites with this identity to
establish exact identity `R.amplitude 2=0`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem root_zero : R.root 0=0 := by simp [root]

/--
The stated quantitative bound `0 ≤ R.root t`.

Use: `«2610.05164v2».Calibration.ReferenceData.amplitude_nonneg` uses this bound to establish
the stated quantitative bound `0 ≤ R.amplitude q`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates `«2610.05164v2».Calibration.ReferenceData.root_zero`,
`«2610.05164v2».Calibration.ReferenceData.root_spec` with the arguments shown in the proof.
-/
theorem root_nonneg {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) : 0 ≤ R.root t := by
  rcases eq_or_lt_of_le ht.1 with h0 | hp
  · rw [← h0,R.root_zero]
  · exact (R.root_spec ⟨hp,ht.2⟩).1.le

/--
Exact identity `cubic R.k t (2*R.b t*t) (R.root t)=0`.

Use: `«2610.05164v2».Calibration.ReferenceData.amplitude_equation` uses this identity to
establish exact identity `R.k*(R.amplitude q)^3-3*Q q*R.amplitude q-2*R.b (Q q)*Q q=0`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates `«2610.05164v2».Calibration.ReferenceData.root_zero`,
`«2610.05164v2».Calibration.ReferenceData.root_spec` with the arguments shown in the proof.
-/
theorem root_equation {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    cubic R.k t (2*R.b t*t) (R.root t)=0 := by
  rcases eq_or_lt_of_le ht.1 with h0 | hp
  · rw [← h0,R.root_zero]; simp [cubic]
  · exact (R.root_spec ⟨hp,ht.2⟩).2

/--
Continuity on the stated domain: `ContinuousOn R.root (Icc (0:ℝ) 1)`.

Use: `«2610.05164v2».Calibration.ReferenceData.amplitude_continuousOn` uses this continuity
result to establish continuity on the stated domain: `ContinuousOn R.amplitude (Icc (0:ℝ) 2)`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Separate `a < 0` from its negation; prove the goal under each of these mutually
exclusive hypotheses. Assume the failure of the desired conclusion and derive a contradiction
from the available bounds/identities. Intersect the eventual or almost-everywhere hypotheses,
then prove the asserted relation at an arbitrary point in that intersection.
-/
theorem root_continuousOn : ContinuousOn R.root (Icc (0:ℝ) 1) := by
  -- Establish continuity hpoly before using the function at limits or in calculus arguments.
  have hpoly (v : ℝ) : Continuous (fun t => cubic R.k t (2*R.coefficient t*t) v) := by
    unfold cubic
    exact ((continuous_const.sub (continuous_const.mul continuous_id |>.mul continuous_const)).sub
      ((continuous_const.mul R.coefficient_continuous).mul continuous_id))
  intro t ht
  apply tendsto_order.2
  constructor
  · intro a ha
    by_cases ha0 : a < 0
    · filter_upwards [self_mem_nhdsWithin] with t' ht'
      exact ha0.trans_le (R.root_nonneg ht')
    · have hp : 0 < t := by
        by_contra h
        have he : t=0 := le_antisymm (not_lt.mp h) ht.1
        rw [he,R.root_zero] at ha
        linarith
      have hb := R.positive t ht
      have ha' : a < positiveRoot R.k t (2*R.b t*t) := by
        simpa only [root,ite_eq_left hp,R.coefficient_eq ht] using ha
      have hn := (cubic_neg_iff R.k_positive hp.le
        (by positivity : 0 < 2*R.b t*t) (not_lt.mp ha0)).2 ha'
      rw [← R.coefficient_eq ht] at hn
      have he := (hpoly a).continuousAt.eventually (gt_mem_nhds hn)
      filter_upwards [he.filter_mono nhdsWithin_le_nhds,
        (lt_mem_nhds hp).filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with t' he hp' ht'
      rw [R.coefficient_eq ht'] at he
      have hb' := R.positive t' ht'
      have h := (cubic_neg_iff R.k_positive hp'.le (by positivity : 0 < 2*R.b t'*t')
        (not_lt.mp ha0)).1 he
      simpa only [root,ite_eq_left hp',R.coefficient_eq ht'] using h
  · intro a ha
    have ha0 : 0 < a := (R.root_nonneg ht).trans_lt ha
    have hn : 0 < cubic R.k t (2*R.coefficient t*t) a := by
      rcases eq_or_lt_of_le ht.1 with hz | hp
      · rw [← hz]
        simpa [cubic] using mul_pos R.k_positive (pow_pos ha0 3)
      · rw [R.coefficient_eq ht]
        have hb := R.positive t ht
        apply (cubic_pos_iff R.k_positive hp.le (by positivity) ha0.le).2
        simpa only [root,ite_eq_left hp,R.coefficient_eq ht] using ha
    have he := (hpoly a).continuousAt.eventually (lt_mem_nhds hn)
    filter_upwards [he.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with t' he ht'
    rcases eq_or_lt_of_le ht'.1 with hz | hp
    · simpa only [← hz,R.root_zero] using ha0
    · rw [R.coefficient_eq ht'] at he
      have hb := R.positive t' ht'
      have h := (cubic_pos_iff R.k_positive hp.le (by positivity) ha0.le).1 he
      simpa only [root,ite_eq_left hp,R.coefficient_eq ht'] using h

/--
The precise assertion is `StrictMonoOn R.root (Icc (0:ℝ) 1)`.

Use: `«2610.05164v2».Calibration.ReferenceData.amplitude_cube_bound` uses this assertion to
establish the stated quantitative bound `(R.amplitude q)^3 ≤ R.cubeConstant*Q q`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates `«2610.05164v2».Calibration.ReferenceData.root_zero`,
`«2610.05164v2».Calibration.ReferenceData.root_spec`,
`«2610.05164v2».Calibration.cubic_neg_iff` with the arguments shown in the proof.
-/
theorem root_strictMono : StrictMonoOn R.root (Icc (0:ℝ) 1) := by
  -- Use the identities/estimates `«2610.05164v2».Calibration.ReferenceData.root_zero`,
  -- `«2610.05164v2».Calibration.ReferenceData.root_spec`,
  -- `«2610.05164v2».Calibration.cubic_neg_iff` with the arguments shown in the proof.
  intro t ht u hu htu
  have hu0 : 0 < u := ht.1.trans_lt htu
  rcases eq_or_lt_of_le ht.1 with hz | hp
  · rw [← hz,R.root_zero]
    exact (R.root_spec ⟨hu0,hu.2⟩).1
  · have hν := R.root_spec ⟨hp,ht.2⟩
    have hb := R.positive t ht
    have hbu := R.positive u hu
    have hmono := R.monotone ht hu htu.le
    have hprod : R.b t*t < R.b u*u :=
      (mul_lt_mul_of_pos_left htu hb).trans_le (mul_le_mul_of_nonneg_right hmono hu0.le)
    have hn : cubic R.k u (2*R.b u*u) (R.root t) < 0 := by
      unfold cubic at *
      nlinarith
    have h := (cubic_neg_iff R.k_positive hu0.le (by positivity) hν.1.le).1 hn
    simpa only [root,ite_eq_left hu0,R.coefficient_eq hu] using h

/--
Defines `amplitude` of type `ℝ` by `R.root (Q q)`.

Use: `«2610.05164v2».Calibration.ReferenceData.amplitude_reflection` uses this definition to
establish exact identity `R.amplitude (2-q)=R.amplitude q`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.
-/
def amplitude (q : ℝ) : ℝ := R.root (Q q)
/--
Defines `speed` of type `ℝ` by `R.k*(R.amplitude q)^2-Q q`.

Use: `«2610.05164v2».Calibration.ReferenceData.speed_gt_two_Q` uses this definition to
establish the stated quantitative bound `2*Q q < R.speed q`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.
-/
def speed (q : ℝ) : ℝ := R.k*(R.amplitude q)^2-Q q

/--
Membership in the specified domain/enclosure: `Q q ∈ Icc (0:ℝ) 1`.

Use: `«2610.05164v2».Calibration.ReferenceData.amplitude_continuousOn` uses this assertion to
establish continuity on the stated domain: `ContinuousOn R.amplitude (Icc (0:ℝ) 2)`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates `«2610.05164v2».Calibration.Q_nonneg` with the arguments
shown in the proof.
-/
theorem Q_mem {q : ℝ} (hq : q ∈ Icc (0:ℝ) 2) : Q q ∈ Icc (0:ℝ) 1 :=
  ⟨Q_nonneg hq,by unfold Q; nlinarith [sq_nonneg (q-1)]⟩

/--
Continuity on the stated domain: `ContinuousOn R.amplitude (Icc (0:ℝ) 2)`.

Use: `«2610.05164v2».Calibration.ReferenceData.profile` uses this continuity result in the
displayed construction of `profile`. Its inputs and component formulas are fixed by that
definition.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates
`«2610.05164v2».Calibration.ReferenceData.root_continuousOn`,
`«2610.05164v2».Calibration.ReferenceData.Q_mem` with the arguments shown in the proof.
-/
theorem amplitude_continuousOn : ContinuousOn R.amplitude (Icc (0:ℝ) 2) :=
  R.root_continuousOn.comp (by unfold Q; fun_prop) (fun _ hq => Q_mem hq)

/--
Exact identity `R.k*(R.amplitude q)^3-3*Q q*R.amplitude q-2*R.b (Q q)*Q q=0`.

Use: `«2610.05164v2».Calibration.ReferenceData.speed_gt_two_Q` uses this identity to establish
the stated quantitative bound `2*Q q < R.speed q`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates `«2610.05164v2».Calibration.ReferenceData.root_equation`,
`«2610.05164v2».Calibration.ReferenceData.Q_mem` with the arguments shown in the proof.
-/
theorem amplitude_equation {q : ℝ} (hq : q ∈ Icc (0:ℝ) 2) :
    R.k*(R.amplitude q)^3-3*Q q*R.amplitude q-2*R.b (Q q)*Q q=0 :=
  R.root_equation (Q_mem hq)

/--
The stated quantitative bound `0 < R.amplitude q`.

Use: `«2610.05164v2».Calibration.ReferenceData.speed_gt_two_Q` uses this bound to establish the
stated quantitative bound `2*Q q < R.speed q`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates `«2610.05164v2».Calibration.ReferenceData.root_spec`,
`«2610.05164v2».Calibration.Q_positive`, `«2610.05164v2».Calibration.ReferenceData.Q_mem` with
the arguments shown in the proof.
-/
theorem amplitude_positive {q : ℝ} (hq : q ∈ Ioo (0:ℝ) 2) : 0 < R.amplitude q :=
  (R.root_spec ⟨Q_positive hq,(Q_mem ⟨hq.1.le,hq.2.le⟩).2⟩).1

/--
The stated quantitative bound `0 ≤ R.amplitude q`.

Use: `«2610.05164v2».Calibration.ReferenceData.density_strictMono_left` uses this bound to
establish the precise assertion is `StrictMonoOn R.density (Icc (R.referenceSpeed.X 0) 0)`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates `«2610.05164v2».Calibration.ReferenceData.root_nonneg`,
`«2610.05164v2».Calibration.ReferenceData.Q_mem` with the arguments shown in the proof.
-/
theorem amplitude_nonneg {q : ℝ} (hq : q ∈ Icc (0:ℝ) 2) : 0 ≤ R.amplitude q :=
  R.root_nonneg (Q_mem hq)

/--
Exact identity `R.amplitude 0=0`.

Use: `«2610.05164v2».Calibration.ReferenceData.coordinate_derivative_nonneg` rewrites with this
identity to prove the bound `0 ≤ R.k*R.density x-Q (R.referenceSpeed.q
x)`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates `«2610.05164v2».Calibration.ReferenceData.root_zero` with
the arguments shown in the proof.
-/
theorem amplitude_zero : R.amplitude 0=0 := by simp [amplitude,Q,R.root_zero]
/--
Exact identity `R.amplitude 2=0`.

Use: `«2610.05164v2».Calibration.ReferenceData.coordinate_derivative_nonneg` rewrites with this
identity to prove the bound `0 ≤ R.k*R.density x-Q (R.referenceSpeed.q
x)`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates `«2610.05164v2».Calibration.ReferenceData.root_zero` with
the arguments shown in the proof.
-/
theorem amplitude_two : R.amplitude 2=0 := by simp [amplitude,Q,R.root_zero]

/--
Exact identity `R.amplitude (2-q)=R.amplitude q`.

Use: `«2610.05164v2».Calibration.ReferenceData.X_reflection` uses this identity to establish
the precise assertion is `R.referenceSpeed.X (2-q)= -R.referenceSpeed.X q`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem amplitude_reflection (q : ℝ) : R.amplitude (2-q)=R.amplitude q := by
  unfold amplitude
  congr 1
  unfold Q
  ring

/--
The stated quantitative bound `2*Q q < R.speed q`.

Use: `«2610.05164v2».Calibration.ReferenceData.speed_gt_two_thirds` uses this bound to
establish the stated quantitative bound `2/3*R.k*(R.amplitude q)^2 < R.speed q`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates
`«2610.05164v2».Calibration.ReferenceData.amplitude_positive`,
`«2610.05164v2».Calibration.ReferenceData.amplitude_equation`,
`«2610.05164v2».Calibration.ReferenceData.Q_mem` with the arguments shown in the proof.
-/
theorem speed_gt_two_Q {q : ℝ} (hq : q ∈ Ioo (0:ℝ) 2) : 2*Q q < R.speed q := by
  have hν := R.amplitude_positive hq
  have he := R.amplitude_equation ⟨hq.1.le,hq.2.le⟩
  have hb := R.positive (Q q) (Q_mem ⟨hq.1.le,hq.2.le⟩)
  have hQ := Q_positive hq
  unfold speed
  nlinarith

end ReferenceData
end
end «2610.05164v2».Calibration
