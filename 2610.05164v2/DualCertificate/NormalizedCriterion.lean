import «2610.05164v2».DualCertificate.FaceReduction
import «2610.05164v2».Residual.Pointwise

/-!
Article: 2610.05164v2, Lemma 16.
The exact scalar normalization (50), prior to endpoint extension.
Use: `«2610.05164v2».DualCertificate.normalized_residual_criterion` feeds
`«2610.05164v2».DualCertificate.NormalizedCalibration.actual_normalized_criterion` (actual
normalized criterion).
Proof chain: `«2610.05164v2».DualCertificate.Data.admissible_analytic` — 2610.05164v2, Theorem E.1;
Stability of strict admissibility and uniform transfer of the certificate value.
-/
namespace «2610.05164v2».DualCertificate
noncomputable section
open «2610.05164v2».Residual
set_option autoImplicit false

 /--
Equivalence of the displayed criteria: `conjugate ν (a-(-τ*Q/d+ν*e)-bΨ)≤ criterionRhs κ ν Q
(-τ*Q/d+ν*e) τ bΨ dΨ ↔ criterion ((a+τ*Q/d-bΨ)/ν) ((bΨ*ν^2-dΨ)/ν^3) e (Q/(κ*ν^2))≤0`.

Use: `«2610.05164v2».DualCertificate.normalized_residual_criterion` uses this bound to
establish equivalence of the displayed criteria: `(∀ n : ℝ, 0≤n → 0≤residual κ ν Q a
(-τ*Q/d+ν*e) τ bΨ dΨ n) ↔ criterion ((a+τ*Q/d-bΨ)/ν) ((bΨ*ν^2-dΨ)/ν^3) e (Q/(κ*ν^2))≤0`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem normalized_state_criterion {κ ν Q d : ℝ} (hκ : κ≠0) (hν : 0<ν)
    (hd : d≠0) (hspeed : d=κ*ν^2-Q) (a τ bΨ dΨ e : ℝ) :
    conjugate ν (a-(-τ*Q/d+ν*e)-bΨ)≤
      criterionRhs κ ν Q (-τ*Q/d+ν*e) τ bΨ dΨ ↔
    criterion ((a+τ*Q/d-bΨ)/ν) ((bΨ*ν^2-dΨ)/ν^3) e (Q/(κ*ν^2))≤0 := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  rw [conjugate_scale hν,regular_price_rhs hd hκ _ _ _ _ _ _ hspeed]
  have he : (a-(-τ*Q/d+ν*e)-bΨ)/ν=(a+τ*Q/d-bΨ)/ν-e := by
    field_simp
    ring
  rw [he]
  have hn : 0<ν^3 := pow_pos hν _
  rw [← div_le_div_iff_of_pos_right hn]
  rw [mul_div_cancel_left₀ _ hn.ne']
  have hr : (ν*e*d/κ+bΨ*ν^2-dΨ)/ν^3=
      (bΨ*ν^2-dΨ)/ν^3+e*(1-Q/(κ*ν^2)) := by
    rw [hspeed]
    field_simp
    ring
  rw [hr]
  unfold criterion
  constructor <;> intro h <;> linarith

 /--
Equivalence of the displayed criteria: `(∀ n : ℝ, 0≤n → 0≤residual κ ν Q a (-τ*Q/d+ν*e) τ bΨ dΨ
n) ↔ criterion ((a+τ*Q/d-bΨ)/ν) ((bΨ*ν^2-dΨ)/ν^3) e (Q/(κ*ν^2))≤0`.

Use: `«2610.05164v2».DualCertificate.NormalizedCalibration.actual_normalized_criterion`
rewrites with this bound to establish the bound stated in that declaration.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Proof: Use the identities/estimates `«2610.05164v2».Residual.pointwise_criterion`,
`«2610.05164v2».DualCertificate.normalized_state_criterion` with the arguments shown in the
proof.
-/
theorem normalized_residual_criterion {κ ν Q d : ℝ} (hκ : κ≠0) (hν : 0<ν)
    (hd : d≠0) (hspeed : d=κ*ν^2-Q) (a τ bΨ dΨ e : ℝ) :
    (∀ n : ℝ, 0≤n → 0≤residual κ ν Q a (-τ*Q/d+ν*e) τ bΨ dΨ n) ↔
    criterion ((a+τ*Q/d-bΨ)/ν) ((bΨ*ν^2-dΨ)/ν^3) e (Q/(κ*ν^2))≤0 := by
  rw [pointwise_criterion hκ]
  exact normalized_state_criterion hκ hν hd hspeed a τ bΨ dΨ e

end
end «2610.05164v2».DualCertificate
