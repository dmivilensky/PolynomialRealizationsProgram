import krylov.Functions.RankOneCriticalMinimum

/-!
Article: main_krylov, thm:LB, uniform genuine source minimizers.
Use: bounded inverse and true quadratic coercivity construct an actual
minimum on a fixed ball and its true Hessian metric uniformly over all
bounded cubic parameters. Source: explicit critical root, actual Hessian
drift and the proved exact endpoint-Hessian minimum identity.
-/
namespace krylov.Functions
noncomputable section
open Set krylov.Convergence
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A genuine norm perturbation of a coercive actual operator retains
the expected quadratic lower form. Article: thm:LB, true source metric. -/
theorem rankOne_form_perturbation (Q B : E →L[ℝ] E) (m delta : ℝ)
    (hQ : ∀ v : E,m*‖v‖^2 ≤ inner ℝ v (Q v)) (hB : ‖B-Q‖≤delta) (v : E) :
    (m-delta)*‖v‖^2 ≤ inner ℝ v (B v) := by
  have hv := ((B-Q).le_opNorm v).trans
    (mul_le_mul_of_nonneg_right hB (norm_nonneg v))
  have hi := (abs_real_inner_le_norm v ((B-Q) v)).trans
    (mul_le_mul_of_nonneg_left hv (norm_nonneg v))
  simp only [_root_.sub_apply,inner_sub_right] at hi
  have hl := (abs_le.mp hi).1
  nlinarith only [hl,hQ v]

/-- The actual cubic Hessian is uniformly coercive throughout a fixed
ball, directly from the primitive quadratic lower bound and |t|≤M.
Article: main_krylov, thm:LB. -/
theorem rankOneCubic_uniform_hessian (Q : E →L[ℝ] E) (a : E) (t M m R : ℝ)
    (hM : 0≤M) (ht : |t|≤M)
    (hQ : ∀ v : E,m*‖v‖^2 ≤ inner ℝ v (Q v))
    (hsmall : M*‖a‖^3*R≤m/2) (x : E) (hx : ‖x‖≤R) (v : E) :
    m/2*‖v‖^2 ≤ inner ℝ v (oneGradientCubicHessian Q a t x v) := by
  have hd : ‖oneGradientCubicHessian Q a t x-Q‖≤m/2 := by
    calc
      _≤|t| *‖a‖^3*‖x‖ := rankOneCubic_hessian_drift Q a x t
      _≤M*‖a‖^3*R := by gcongr
      _≤m/2 := hsmall
  have hh := rankOne_form_perturbation Q (oneGradientCubicHessian Q a t x) m (m/2) hQ hd v
  nlinarith only [hh]

/-- The explicitly constructed branch is a genuine minimum on the full
fixed ball and has the actual uniform true-Hessian drift. Its parameters
may be arbitrary functions of the last query or shrinking scale.
Article: main_krylov, thm:LB. -/
theorem rankOneCriticalPoint_uniform_minimum (Q Rinv : E →L[ℝ] E)
    (hQsym : Q.toLinearMap.IsSymmetric) (hQR : ∀ v : E,Q (Rinv v)=v)
    (g a : E) (t M K m R : ℝ) (hM : 0≤M) (hK : 0≤K) (hm : 0<m)
    (ht : |t|≤M) (hR : ‖Rinv‖≤K)
    (hQ : ∀ v : E,m*‖v‖^2 ≤ inner ℝ v (Q v))
    (hsmall : 2*M*K^2*‖a‖^3*‖g‖≤1)
    (hball : 2*K*‖g‖≤R) (hpositive : M*‖a‖^3*R≤m/2) :
    let x := rankOneCriticalPoint Rinv g a t
    oneGradientCubicGradient Q g a t x=0 ∧
      IsMinOn (oneGradientCubicObjective Q g a t) {z | ‖z‖≤R} x ∧
      ‖x‖≤2*K*‖g‖ ∧ ‖x+Rinv g‖≤2*M*K^3*‖a‖^3*‖g‖^2 ∧
      ‖oneGradientCubicHessian Q a t x-Q‖≤2*M*K*‖a‖^3*‖g‖ ∧
      ∀ v : E,m/2*‖v‖^2 ≤ inner ℝ v (oneGradientCubicHessian Q a t x v) := by
  have hb := rankOneCriticalPoint_bounds Rinv g a t M K hM hK ht hR hsmall
  have hc := rankOneCriticalPoint_critical Q Rinv hQR g a t hb.1
  have hx := hb.2.2.trans hball
  have hpos := rankOneCubic_uniform_hessian Q a t M m R hM ht hQ hpositive
  have hmin := (rankOneCubic_critical_minimum Q hQsym g a t (m/2) (by positivity)
    {z | ‖z‖≤R} _ hx hc (fun z hz=>hpos z hz)).1
  refine ⟨hc,hmin,hb.2.2,hb.2.1,?_,hpos _ hx⟩
  calc
    _≤|t| *‖a‖^3*‖rankOneCriticalPoint Rinv g a t‖ := rankOneCubic_hessian_drift _ _ _ _
    _≤M*‖a‖^3*(2*K*‖g‖) := by gcongr;exact hb.2.2
    _=_ := by ring

end
end krylov.Functions
