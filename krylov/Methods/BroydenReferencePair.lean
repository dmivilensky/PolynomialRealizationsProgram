import krylov.Methods.BroydenUpdate

set_option autoImplicit false
/-!
Article: main_krylov, def:classes, actual convex Broyden CG pair algebra.
Use: derive the genuine positive DFP and BFGS direction scales from a real consecutive orthogonal CG gradient pair.
Source: standard Dixon/Nazareth secant-update equivalence, proved here from the actual inverse endpoint maps, true gradient orthogonality and genuine exact-search pairings.
-/

namespace krylov.Methods
noncomputable section
open krylov.Reference
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual consecutive CG pair determines the genuine inverse-curvature and secant pairings exactly.
Use: The actual consecutive CG pair determines the genuine inverse-curvature and secant pairings exactly.
Article: main_krylov, def:classes, actual convex Broyden CG pair algebra.
Proof: Expand the real linear-map gradient difference and use the true orthogonal gradient and direction pairings. -/
theorem broyden_reference_pair_data (H : E →ₗ[ℝ] E) (g r d : E) (c a α : ℝ)
    (hg : H g= -a • d) (hr : H r=c • r)
    (hgd : inner ℝ g d= -‖g‖^2) (hrd : inner ℝ r d=0) (hgr : inner ℝ g r=0) :
    inner ℝ (r-g) (H (r-g))=c*‖r‖^2+a*‖g‖^2 ∧
    inner ℝ (α • d) (r-g)=α*‖g‖^2 ∧
    inner ℝ (α • d) r=0 ∧ inner ℝ (r-g) (H r)=c*‖r‖^2 := by
  -- The actual orthogonal reference gradients determine both genuine secant denominators.
  have hdg : inner ℝ d g= -‖g‖^2 := by rw [real_inner_comm];exact hgd
  have hdr : inner ℝ d r=0 := by rw [real_inner_comm];exact hrd
  constructor
  · rw [map_sub,hr,hg,inner_sub_left,inner_sub_right,inner_sub_right,
      real_inner_smul_right,real_inner_smul_right,real_inner_smul_right,real_inner_smul_right,
      real_inner_self_eq_norm_sq,hgr,hrd,hgd]
    ring
  · constructor
    · rw [real_inner_smul_left,inner_sub_right,hdr,hdg]
      ring
    · constructor
      · rw [real_inner_smul_left,hdr,mul_zero]
      · rw [hr,real_inner_smul_right,inner_sub_left,real_inner_self_eq_norm_sq,hgr,sub_zero]

/-- The actual inverse DFP endpoint sends the new genuine gradient to its true positive reciprocal direction scale.
Use: The actual inverse DFP endpoint sends the new genuine gradient to its true positive reciprocal direction scale.
Article: main_krylov, def:classes, actual convex Broyden CG pair algebra.
Proof: Use the actual reference pairings, prove the genuine inverse-curvature denominator positive, and simplify the true physical rank-two action. -/
theorem inverseDFPUpdate_reference (H : E →ₗ[ℝ] E) (g r d : E) (c a α : ℝ)
    (hc : 0<c) (ha : 0<a) (hg0 : g≠0)
    (hg : H g= -a • d) (hr : H r=c • r)
    (hgd : inner ℝ g d= -‖g‖^2) (hrd : inner ℝ r d=0) (hgr : inner ℝ g r=0) :
    inverseDFPUpdate H (α • d) (r-g) r=
      (c*a*‖g‖^2/(c*‖r‖^2+a*‖g‖^2)) • (r-(‖r‖^2/‖g‖^2) • d) := by
  -- The true reference pair fixes both actual denominators before simplifying the real inverse update.
  have hp := broyden_reference_pair_data H g r d c a α hg hr hgd hrd hgr
  have hA : 0<‖g‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hg0)
  -- The real inverse-curvature denominator is strictly positive because the genuine previous residual and direction scale are nonzero.
  have hσ : 0<c*‖r‖^2+a*‖g‖^2 := add_pos_of_nonneg_of_pos (mul_nonneg hc.le (sq_nonneg _)) (mul_pos ha hA)
  have h1 : c-(c*‖r‖^2/(c*‖r‖^2+a*‖g‖^2))*c=c*a*‖g‖^2/(c*‖r‖^2+a*‖g‖^2) := by
    field_simp [hσ.ne']
    ring
  have h2 : (c*‖r‖^2/(c*‖r‖^2+a*‖g‖^2))*a=
      (c*a*‖g‖^2/(c*‖r‖^2+a*‖g‖^2))*(‖r‖^2/‖g‖^2) := by
    field_simp [hσ.ne',hA.ne']
  -- Actual scalar coefficient identities identify the genuine vector update with the real next-CG direction.
  rw [inverseDFPUpdate_apply,hp.1,hp.2.2.1,hp.2.2.2,zero_div,zero_smul,add_zero,map_sub,hr,hg]
  rw [neg_smul,sub_neg_eq_add,smul_add,smul_smul,smul_smul,smul_sub,smul_smul,← h2,← h1]
  module

/-- The actual inverse BFGS endpoint sends the new genuine gradient to the true original scalar direction scale.
Use: The actual inverse BFGS endpoint sends the new genuine gradient to the true original scalar direction scale.
Article: main_krylov, def:classes, actual convex Broyden CG pair algebra.
Proof: The genuine old step is orthogonal to the actual new gradient; simplify the real two-loop update and cancel only its true nonzero search and residual factors. -/
theorem inverseBFGSUpdate_reference (H : E →ₗ[ℝ] E) (g r d : E) (c a α : ℝ)
    (hα : α≠0) (hg0 : g≠0)
    (hg : H g= -a • d) (hr : H r=c • r)
    (hgd : inner ℝ g d= -‖g‖^2) (hrd : inner ℝ r d=0) (hgr : inner ℝ g r=0) :
    inverseBFGSUpdate H (α • d) (r-g) r=c • (r-(‖r‖^2/‖g‖^2) • d) := by
  -- The true orthogonal current step removes the backward coefficient before the genuine nonzero scalar cancellation.
  have hp := broyden_reference_pair_data H g r d c a α hg hr hgd hrd hgr
  have hA : ‖g‖^2≠0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hg0)
  have hcoef : ((α*‖g‖^2)⁻¹*(c*‖r‖^2))*α=c*(‖r‖^2/‖g‖^2) := by
    field_simp [hα,hA]
  rw [inverseBFGSUpdate_apply]
  dsimp only
  rw [hp.2.1,hp.2.2.1,mul_zero,zero_smul,sub_zero,hp.2.2.2,hr]
  rw [zero_sub,neg_smul,smul_smul,hcoef,smul_sub,smul_smul]
  module
end
end krylov.Methods
