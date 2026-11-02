import krylov.Convergence.OneGradientFunctions
import krylov.Functions.QuadraticHiddenFamily
import krylov.Functions.RankOneGeometry
import krylov.OneGradient.Information
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
Article: main_krylov, thm:LB, actual rank-one cubic adversary.
Use: work with the real scalar quadratic-plus-rank-one cubic, its true
Riesz gradient and genuine derivatives. No gradient-oracle fields are
postulated independently of an objective.
Source: the explicit polynomial family in Appendix G and scalar product rules.
-/
namespace krylov.Convergence
noncomputable section
open Set Matrix krylov.Methods krylov.Reference krylov.Functions krylov.OneGradient
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The literal quadratic, linear force and rank-one cubic scalar source.
Article: main_krylov, thm:LB, f_(b,t). -/
def oneGradientCubicObjective (Q : E →L[ℝ] E) (g a : E) (t : ℝ) (x : E) : ℝ :=
  quadraticPotential ((innerSL ℝ).comp Q) (-(innerSL ℝ g)) x+(rankOneCubic a t).potential x

/-- Its actual Riesz-gradient formula. Article: thm:LB. -/
def oneGradientCubicGradient (Q : E →L[ℝ] E) (g a : E) (t : ℝ) (x : E) : E :=
  g+Q x+(t/2*(inner ℝ a x)^2) • a

/-- Its true physical Hessian field. Article: thm:LB. -/
def oneGradientCubicHessian (Q : E →L[ℝ] E) (a : E) (t : ℝ) (x : E) : E →L[ℝ] E :=
  Q+(t*inner ℝ a x) • InnerProductSpace.rankOne ℝ a a

/-- The scalar source is exactly the polynomial printed in the article.
Article: main_krylov, thm:LB. -/
theorem oneGradientCubicObjective_eq (Q : E →L[ℝ] E) (g a : E) (t : ℝ) (x : E) :
    oneGradientCubicObjective Q g a t x=inner ℝ (Q x) x/2+inner ℝ g x+t/6*(inner ℝ a x)^3 := by
  simp only [oneGradientCubicObjective,quadraticPotential,ContinuousLinearMap.comp_apply,
    innerSL_apply_apply,_root_.neg_apply,sub_neg_eq_add,SymmetricCubic.potential,rankOneCubic_apply]
  ring

/-- This genuine scalar polynomial is smooth to every finite order.
Article: main_krylov, thm:LB. -/
theorem oneGradientCubicObjective_contDiff (Q : E →L[ℝ] E) (g a : E) (t : ℝ) (r : ℕ) :
    ContDiff ℝ r (oneGradientCubicObjective Q g a t) := by
  rw [funext (oneGradientCubicObjective_eq Q g a t)]
  have hquad : ContDiff ℝ r (fun x : E=>inner ℝ (Q x) x) := Q.contDiff.inner ℝ contDiff_id
  have hlin : ContDiff ℝ r (fun x : E=>inner ℝ g x) := contDiff_const.inner ℝ contDiff_id
  have hphi : ContDiff ℝ r (fun x : E=>inner ℝ a x) := contDiff_const.inner ℝ contDiff_id
  exact ((hquad.div_const 2).add hlin).add (contDiff_const.mul (hphi.pow 3))

/-- The displayed vector field is the true scalar derivative, with no
independent-oracle premise. Article: main_krylov, thm:LB. -/
theorem oneGradientCubicObjective_hasFDerivAt (Q : E →L[ℝ] E)
    (hQ : Q.toLinearMap.IsSymmetric) (g a : E) (t : ℝ) (x : E) :
    HasFDerivAt (oneGradientCubicObjective Q g a t)
      (innerSL ℝ (oneGradientCubicGradient Q g a t x)) x := by
  have hA (u v : E) : ((innerSL ℝ).comp Q) u v=((innerSL ℝ).comp Q) v u := by
    exact (hQ u v).trans (real_inner_comm _ _)
  have hh := (quadraticPotential_hasFDerivAt ((innerSL ℝ).comp Q) (-(innerSL ℝ g)) hA x).add
    ((rankOneCubic a t).potential_hasFDerivAt x)
  have he : innerSL ℝ (oneGradientCubicGradient Q g a t x)=
      (((innerSL ℝ).comp Q) x-(-(innerSL ℝ g)))+(1/2:ℝ) • (rankOneCubic a t).form x x := by
    ext v
    simp only [oneGradientCubicGradient,innerSL_apply_apply,inner_add_left,real_inner_smul_left,
      _root_.add_apply,ContinuousLinearMap.comp_apply,
      sub_neg_eq_add,_root_.smul_apply,rankOneCubic_apply,smul_eq_mul]
    ring
  rw [he]
  exact hh

/-- The true gradient differentiates to the actual affine Hessian.
Article: main_krylov, thm:LB. -/
theorem oneGradientCubicGradient_hasFDerivAt (Q : E →L[ℝ] E) (g a : E) (t : ℝ) (x : E) :
    HasFDerivAt (oneGradientCubicGradient Q g a t) (oneGradientCubicHessian Q a t x) x := by
  have hs := (((innerSL ℝ a).hasFDerivAt (x:=x)).pow 2).const_mul (t/2)
  have hs' : HasFDerivAt (fun y : E=>t/2*(innerSL ℝ a y)^2)
      ((t*innerSL ℝ a x) • innerSL ℝ a) x := by
    convert hs using 1
    ext v
    simp only [_root_.smul_apply,smul_eq_mul,two_smul,Nat.reduceSub,pow_one]
    ring
  have hv := hs'.smul_const a
  have hh := ((hasFDerivAt_const g x).add (Q.hasFDerivAt (x:=x))).add hv
  have he : oneGradientCubicHessian Q a t x=0+Q+((t*innerSL ℝ a x) • innerSL ℝ a).smulRight a := by
    ext v
    simp only [oneGradientCubicHessian,_root_.add_apply,zero_add,
      _root_.smul_apply,ContinuousLinearMap.smulRight_apply,innerSL_apply_apply,
      InnerProductSpace.rankOne_apply,smul_smul,smul_eq_mul]
  rw [he]
  have hfun : oneGradientCubicGradient Q g a t=
      ((fun _ : E=>g)+(fun y=>Q y)+(fun y=>(t/2*(innerSL ℝ a y)^2) • a)) := by
    funext y
    change g+Q y+(t/2*(inner ℝ a y)^2) • a=g+Q y+(t/2*(innerSL ℝ a y)^2) • a
    rw [innerSL_apply_apply]
  rw [hfun]
  exact hh

/-- Rank-one cubics give exactly the quadratic gradient whenever the
hidden coordinate vanishes. Article: thm:LB, common Krylov prefix. -/
theorem oneGradientCubicGradient_eq_of_hidden_zero (Q : E →L[ℝ] E) (g a : E) (t : ℝ)
    (x : E) (hx : inner ℝ a x=0) : oneGradientCubicGradient Q g a t x=g+Q x := by
  simp only [oneGradientCubicGradient,hx,zero_pow (by decide : 2≠0),mul_zero,zero_smul,add_zero]

/-- The genuine constant third derivative of the rank-one cubic source.
Article: main_krylov, thm:LB, physical t times a tensor cube. -/
def oneGradientCubicThird (a : E) (t : ℝ) : E →L[ℝ] E →L[ℝ] E :=
  (t • innerSL ℝ a).smulRight (InnerProductSpace.rankOne ℝ a a)

/-- The displayed true Hessian differentiates to the actual constant
rank-one third derivative, at every real point. Article: thm:LB. -/
theorem oneGradientCubicHessian_hasFDerivAt (Q : E →L[ℝ] E) (a : E) (t : ℝ) (x : E) :
    HasFDerivAt (oneGradientCubicHessian Q a t) (oneGradientCubicThird a t) x := by
  have hh := (hasFDerivAt_const Q x).add
    (((t • innerSL ℝ a).hasFDerivAt (x:=x)).smul_const (InnerProductSpace.rankOne ℝ a a))
  have hfun : oneGradientCubicHessian Q a t=
      (fun _ : E=>Q)+(fun y=>(t*inner ℝ a y) • InnerProductSpace.rankOne ℝ a a) := rfl
  rw [hfun]
  simpa only [oneGradientCubicThird,zero_add,
    _root_.smul_apply,smul_eq_mul,innerSL_apply_apply] using hh

/-- Exact three-slot pairing of the genuine physical third derivative.
Article: main_krylov, thm:LB. -/
theorem oneGradientCubicThird_pair (a : E) (t : ℝ) (u v w : E) :
    inner ℝ (oneGradientCubicThird a t u v) w=(rankOneCubic a t).form u v w := by
  simp only [oneGradientCubicThird,ContinuousLinearMap.smulRight_apply,
    _root_.smul_apply,smul_eq_mul,innerSL_apply_apply,InnerProductSpace.rankOne_apply,
    smul_smul,real_inner_smul_left,rankOneCubic_apply]

end
end krylov.Convergence
