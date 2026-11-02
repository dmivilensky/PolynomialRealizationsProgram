import krylov.Functions.RankOneCriticalPoint

/-!
Article: main_krylov, thm:LB, actual minimum of the cubic adversary.
Use: derive minimization and Hessian drift of the genuine critical branch
from its explicit polynomial; neither is included as a certificate field.
Source: the exact one-third/one-sixth endpoint Hessian identity for cubics.
-/
namespace krylov.Functions
noncomputable section
open Set krylov.Convergence
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Exact cubic Taylor identity using the two actual endpoint Hessians.
Article: main_krylov, thm:LB, true minimum. -/
theorem rankOneCubic_endpoint_identity (Q : E →L[ℝ] E)
    (hQ : Q.toLinearMap.IsSymmetric) (g a : E) (t : ℝ) (x y : E) :
    oneGradientCubicObjective Q g a t y-oneGradientCubicObjective Q g a t x-
      inner ℝ (oneGradientCubicGradient Q g a t x) (y-x)=
      (1/3:ℝ)*inner ℝ (y-x) (oneGradientCubicHessian Q a t x (y-x))+
        (1/6:ℝ)*inner ℝ (y-x) (oneGradientCubicHessian Q a t y (y-x)) := by
  have hxx : inner ℝ (Q x) x=inner ℝ x (Q x) := real_inner_comm _ _
  have hyy : inner ℝ (Q y) y=inner ℝ y (Q y) := real_inner_comm _ _
  have hxy : inner ℝ (Q x) y=inner ℝ y (Q x) := real_inner_comm _ _
  have hyx : inner ℝ x (Q y)=inner ℝ y (Q x) := (hQ x y).symm.trans hxy
  have hax : inner ℝ x a=inner ℝ a x := real_inner_comm _ _
  have hay : inner ℝ y a=inner ℝ a y := real_inner_comm _ _
  simp only [oneGradientCubicObjective_eq,oneGradientCubicGradient,oneGradientCubicHessian,
    _root_.add_apply,_root_.smul_apply,InnerProductSpace.rankOne_apply,map_sub,
    inner_add_left,inner_add_right,inner_sub_left,inner_sub_right,real_inner_smul_left,
    real_inner_smul_right,hxx,hyy,hxy,hyx,hax,hay]
  ring

/-- Every true critical point minimizes the entire actual cubic on its
positive-Hessian domain, with the genuine quadratic gap.
Article: main_krylov, thm:LB. -/
theorem rankOneCubic_critical_minimum (Q : E →L[ℝ] E)
    (hQ : Q.toLinearMap.IsSymmetric) (g a : E) (t m : ℝ) (hm : 0≤m)
    (U : Set E) (x : E) (hx : x∈U)
    (hcritical : oneGradientCubicGradient Q g a t x=0)
    (hlower : ∀ z∈U,∀ v : E,m*‖v‖^2 ≤ inner ℝ v (oneGradientCubicHessian Q a t z v)) :
    IsMinOn (oneGradientCubicObjective Q g a t) U x ∧
      ∀ y∈U,m/2*‖y-x‖^2≤oneGradientCubicObjective Q g a t y-oneGradientCubicObjective Q g a t x := by
  have hgap (y : E) (hy : y∈U) := rankOneCubic_endpoint_identity Q hQ g a t x y
  have hg (y : E) (hy : y∈U) :
      m/2*‖y-x‖^2≤oneGradientCubicObjective Q g a t y-oneGradientCubicObjective Q g a t x := by
    have hh := hgap y hy
    rw [hcritical,inner_zero_left,sub_zero] at hh
    have h0 := hlower x hx (y-x)
    have h1 := hlower y hy (y-x)
    linarith only [hh,h0,h1]
  refine ⟨?_,hg⟩
  intro y hy
  exact sub_nonneg.mp ((by positivity : 0≤m/2*‖y-x‖^2).trans (hg y hy))

/-- The actual cubic Hessian has its literal uniform operator drift.
Article: main_krylov, thm:LB. -/
theorem rankOneCubic_hessian_drift (Q : E →L[ℝ] E) (a x : E) (t : ℝ) :
    ‖oneGradientCubicHessian Q a t x-Q‖≤|t| *‖a‖^3*‖x‖ := by
  rw [oneGradientCubicHessian,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,
    abs_mul,InnerProductSpace.norm_rankOne]
  have hh := mul_le_mul_of_nonneg_left (abs_real_inner_le_norm a x) (abs_nonneg t)
  have hs := mul_le_mul_of_nonneg_right hh (by positivity : 0≤‖a‖*‖a‖)
  nlinarith only [hs]

end
end krylov.Functions
