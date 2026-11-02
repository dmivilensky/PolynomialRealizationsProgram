import krylov.OneGradient.InformedPriorBase
import krylov.OneGradient.CanonicalLastNormal
set_option autoImplicit false
/-!
Article: main_krylov, thm:local(b), exact physical prior in the true moving frame.
Use: realize the original known-prior attaining rank-one form in the
actual perturbed reference's own positive-root/last-CG coordinates.
Source: genuine physical prior family, exact common final CG state and
actual last-normal canonical transport; no hypothetical canonical prior.
-/

namespace krylov.OneGradient
noncomputable section
open Matrix krylov.Reference krylov.Secant krylov.LinearAlgebra
open scoped Matrix.Norms.L2Operator
variable {n : ℕ}

/-- The original physical known-prior base family has exactly the
canonical prior coefficient rho/(1+rho) in its own genuine last-CG axis.
Use: original physical K_X(c) sharpness uses a real admissible base prior
with the correct leading coefficient, rather than an assumed R field.
Article: main_krylov, thm:local(b), true physical prior realization.
Proof: genuine physical fibre information fixes the actual last residual
and its unit Lanczos normal. Exact last-normal canonical transport gives
the true physical scalar times the actual final CG length; its proved
reciprocal prior formula cancels the original inverse pivot exactly. -/
theorem informedPriorBase_canonical_form
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hg : g≠0)
    (hc : (activeSpectralValues A hA.1 g).card=n+1) (rho : ℝ) (hrho : 0≤ rho) :
    let B := informedPriorBase A hA g hg hc rho
    cgOperator (relativeOperator B (B-A))=(rho/(1+rho)) • InnerProductSpace.rankOne ℝ
      (canonicalCGUnitStep B g n) (canonicalCGUnitStep B g n) := by
  let B := informedPriorBase A hA g hg hc rho
  let z := lastLanczosVector A hA g hg hc
  let alpha := lastInversePivot A hA g hg hc
  let gamma := inner ℝ z (CG.gradient (cgOperator A) g n)
  have hB := informedPriorBase_posDef A hA g hg hc rho hrho
  have hcount := informedPriorBase_full_atoms A hA g hg hc rho hrho
  obtain ⟨hgrad,hgamma⟩ := last_cg_gradient_normal A hA g hg hc
  have hgradB : CG.gradient (cgOperator B) g n=gamma • z :=
    (congrArg CGState.gradient (informedPriorBase_cg_prefix A hA g hg hc rho n le_rfl)).trans hgrad
  have hform := canonical_last_normal_form B hB g hcount z (last_lanczos_unit A hA g hg hc)
    gamma (rho/alpha) hgamma hgradB
  have hdiff : B-A=(rho/alpha) • vecMulVec (WithLp.ofLp z) (WithLp.ofLp z) := by
    simp only [B,informedPriorBase,lanczosCompletion,add_sub_cancel_left]
    rfl
  have hcoef : (rho/alpha)*CG.length (cgOperator B) g n=rho/(1+rho) := by
    rw [informedPriorBase_last_length A hA g hg hc rho hrho,
      ← last_inverse_pivot_cg_length A hA g hg hc]
    dsimp only [alpha]
    field_simp [(last_inverse_pivot_positive A hA g hg hc).ne']
  dsimp only
  rw [hdiff,hform,hcoef]

/-- The actual physical prior's true moving canonical form differs from
rho times its own last-CG-axis projector by at most rho², uniformly in
the original reference and radius, including zero radius.
Use: at rho=c*omega the source prior term is c*omega h hᵀ with a genuine
uniform quadratic remainder, with every physical domain derived.
Article: main_krylov, thm:local(b), actual prior first-order realization.
Proof: its exact coefficient is rho/(1+rho). The genuine last CG axis is
unit, so its real rank-one operator norm is one. The exact coefficient
difference has norm rho²/(1+rho), bounded by rho² for nonnegative rho. -/
theorem informedPriorBase_canonical_remainder
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hg : g≠0)
    (hc : (activeSpectralValues A hA.1 g).card=n+1) (rho : ℝ) (hrho : 0≤ rho) :
    let B := informedPriorBase A hA g hg hc rho
    let H := InnerProductSpace.rankOne ℝ (canonicalCGUnitStep B g n) (canonicalCGUnitStep B g n)
    ‖cgOperator (relativeOperator B (B-A))-rho • H‖≤rho^2 := by
  let B := informedPriorBase A hA g hg hc rho
  let h := canonicalCGUnitStep B g n
  let H := InnerProductSpace.rankOne ℝ h h
  have hB := informedPriorBase_posDef A hA g hg hc rho hrho
  have hcount := informedPriorBase_full_atoms A hA g hg hc rho hrho
  have ho := canonicalCG_frame_of_full_atoms B hB g hcount
  have hh : ‖h‖=1 := ho.norm_eq_one (Fin.last n)
  have hH : ‖H‖=1 := by rw [InnerProductSpace.norm_rankOne,hh,mul_one]
  have hcoef : rho/(1+rho)-rho= -(rho^2/(1+rho)) := by field_simp;ring
  have hden : 0<1+rho := by linarith
  dsimp only
  rw [informedPriorBase_canonical_form A hA g hg hc rho hrho]
  change ‖(rho/(1+rho)) • H-rho • H‖≤rho^2
  have hsub : (rho/(1+rho)) • H-rho • H=(rho/(1+rho)-rho) • H := (sub_smul _ _ H).symm
  rw [hsub,norm_smul]
  rw [hH,mul_one,hcoef,norm_neg,Real.norm_of_nonneg (div_nonneg (sq_nonneg rho) hden.le)]
  exact (div_le_iff₀ hden).mpr (by nlinarith [mul_nonneg (sq_nonneg rho) hrho])

end
end krylov.OneGradient
