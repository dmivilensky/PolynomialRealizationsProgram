import «2610.05164v2».Residual.CubicConjugate

/-!
Article: 2610.05164v2, Proposition 8.
Theorem 3.5's exact amplitude elimination and algebraic gauge invariance.
Use: `«2610.05164v2».Residual.regular_price_rhs` feeds
`«2610.05164v2».DualCertificate.normalized_state_criterion` (normalized state criterion).
-/
namespace «2610.05164v2».Residual
noncomputable section
open «2610.05164v2».Calibration

/--
Defines `residual` of type `ℝ` by `rho n ν-a*(n^2-ν^2)+η/κ*(κ*n^2-Q)+τ/κ*Q+bΨ*n^2-dΨ`.

Use: `«2610.05164v2».Residual.residual_rewrite` uses this definition to establish the precise
assertion is `residual κ ν Q a η τ bΨ dΨ n= criterionRhs κ ν Q η τ bΨ
dΨ-((a-η-bΨ)*(n^2-ν^2)-rho n ν)`.

Article: 2610.05164v2, Theorem 3.5 via `«2610.05164v2».Residual.pointwise_criterion`.
-/
def residual (κ ν Q a η τ bΨ dΨ n : ℝ) : ℝ :=
  rho n ν-a*(n^2-ν^2)+η/κ*(κ*n^2-Q)+τ/κ*Q+bΨ*n^2-dΨ

/--
Defines `criterionRhs` of type `ℝ` by `(η*(κ*ν^2-Q)+τ*Q)/κ+bΨ*ν^2-dΨ`.

Use: `«2610.05164v2».Residual.gauge_rhs` uses this definition to establish the precise
assertion is `criterionRhs κ ν Q (η+κ*t) τ (bΨ-κ*t) (dΨ-Q*t)= criterionRhs κ ν Q η τ bΨ dΨ`.

Article: 2610.05164v2, Theorem 3.5 via `«2610.05164v2».Residual.pointwise_criterion`.
-/
def criterionRhs (κ ν Q η τ bΨ dΨ : ℝ) : ℝ :=
  (η*(κ*ν^2-Q)+τ*Q)/κ+bΨ*ν^2-dΨ

/--
The precise assertion is `residual κ ν Q a η τ bΨ dΨ n= criterionRhs κ ν Q η τ bΨ
dΨ-((a-η-bΨ)*(n^2-ν^2)-rho n ν)`.

Use: `«2610.05164v2».Residual.pointwise_criterion` rewrites with this identity to establish
equivalence of the displayed criteria: `(∀ n : ℝ, 0 ≤ n → 0 ≤ residual κ ν Q a η τ bΨ dΨ n) ↔
conjugate ν (a-η-bΨ) ≤ criterionRhs κ ν Q η τ bΨ dΨ`.

Article: 2610.05164v2, Theorem 3.5 via `«2610.05164v2».Residual.pointwise_criterion`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem residual_rewrite {κ : ℝ} (hκ : κ ≠ 0) (ν Q a η τ bΨ dΨ n : ℝ) :
    residual κ ν Q a η τ bΨ dΨ n=
      criterionRhs κ ν Q η τ bΨ dΨ-((a-η-bΨ)*(n^2-ν^2)-rho n ν) := by
  unfold residual criterionRhs
  field_simp
  ring

/--
Includes the endpoint case ν=0. No positivity assumption is needed on the comparison
multipliers or on the price.

Equivalence of the displayed criteria: `(∀ n : ℝ, 0 ≤ n → 0 ≤ residual κ ν Q a η τ bΨ dΨ n) ↔
conjugate ν (a-η-bΨ) ≤ criterionRhs κ ν Q η τ bΨ dΨ`.

Use: `«2610.05164v2».DualCertificate.AnalyticData.energy_ge_value` uses this bound to establish
the bound stated in that declaration.

Article: 2610.05164v2, Theorem 3.5.

Proof: Use the identities/estimates `«2610.05164v2».Residual.conjugate_le_iff`,
`«2610.05164v2».Residual.residual_rewrite` with the arguments shown in the proof.
-/
theorem pointwise_criterion {κ : ℝ} (hκ : κ ≠ 0) (ν Q a η τ bΨ dΨ : ℝ) :
    (∀ n : ℝ, 0 ≤ n → 0 ≤ residual κ ν Q a η τ bΨ dΨ n) ↔
      conjugate ν (a-η-bΨ) ≤ criterionRhs κ ν Q η τ bΨ dΨ := by
  rw [conjugate_le_iff]
  simp only [residual_rewrite hκ,sub_nonneg]

/--
Exact identity `a-(η+κ*t)-(bΨ-κ*t)=a-η-bΨ`.

Use: `«2610.05164v2».Residual.residual_gauge` rewrites with this identity to establish the
precise assertion is `residual κ ν Q a (η+κ*t) τ (bΨ-κ*t) (dΨ-Q*t) n= residual κ ν Q a η τ bΨ
dΨ n`.

Article: 2610.05164v2, Proposition 8.

Proof: The tactic block explicitly constructs the required witness or reduces the goal to the
local facts stated below.
-/
theorem gauge_argument (κ a η bΨ t : ℝ) : a-(η+κ*t)-(bΨ-κ*t)=a-η-bΨ := by ring

/--
The precise assertion is `criterionRhs κ ν Q (η+κ*t) τ (bΨ-κ*t) (dΨ-Q*t)= criterionRhs κ ν Q η
τ bΨ dΨ`.

Use: `«2610.05164v2».Residual.residual_gauge` rewrites with this identity to establish the
precise assertion is `residual κ ν Q a (η+κ*t) τ (bΨ-κ*t) (dΨ-Q*t) n= residual κ ν Q a η τ bΨ
dΨ n`.

Article: 2610.05164v2, Proposition 8.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem gauge_rhs {κ : ℝ} (hκ : κ ≠ 0) (ν Q η τ bΨ dΨ t : ℝ) :
    criterionRhs κ ν Q (η+κ*t) τ (bΨ-κ*t) (dΨ-Q*t)=
      criterionRhs κ ν Q η τ bΨ dΨ := by
  unfold criterionRhs
  field_simp
  ring

/--
The precise assertion is `residual κ ν Q a (η+κ*t) τ (bΨ-κ*t) (dΨ-Q*t) n= residual κ ν Q a η τ
bΨ dΨ n`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: 2610.05164v2, Proposition 8.

Proof: Use the identities/estimates `«2610.05164v2».Residual.residual_rewrite`,
`«2610.05164v2».Residual.gauge_rhs`, `«2610.05164v2».Residual.gauge_argument` with the
arguments shown in the proof.
-/
theorem residual_gauge {κ : ℝ} (hκ : κ ≠ 0) (ν Q a η τ bΨ dΨ t n : ℝ) :
    residual κ ν Q a (η+κ*t) τ (bΨ-κ*t) (dΨ-Q*t) n=
      residual κ ν Q a η τ bΨ dΨ n := by rw [residual_rewrite hκ,residual_rewrite hκ,gauge_rhs hκ,gauge_argument]

/--
Exact identity `criterionRhs κ ν Q (-τ*Q/d+ν*e) τ bΨ dΨ=ν*e*d/κ+bΨ*ν^2-dΨ`.

Use: `«2610.05164v2».DualCertificate.normalized_state_criterion` rewrites with this identity to
establish equivalence of the displayed criteria: `conjugate ν (a-(-τ*Q/d+ν*e)-bΨ)≤ criterionRhs
κ ν Q (-τ*Q/d+ν*e) τ bΨ dΨ ↔ criterion ((a+τ*Q/d-bΨ)/ν) ((bΨ*ν^2-dΨ)/ν^3) e (Q/(κ*ν^2))≤0`.

Article: 2610.05164v2, Theorem 3.5.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem regular_price_rhs {κ d : ℝ} (hd : d ≠ 0) (hκ : κ ≠ 0)
    (ν Q τ e bΨ dΨ : ℝ) (he : d=κ*ν^2-Q) :
    criterionRhs κ ν Q (-τ*Q/d+ν*e) τ bΨ dΨ=ν*e*d/κ+bΨ*ν^2-dΨ := by
  unfold criterionRhs
  rw [← he]
  field_simp
  ring

end
end «2610.05164v2».Residual
