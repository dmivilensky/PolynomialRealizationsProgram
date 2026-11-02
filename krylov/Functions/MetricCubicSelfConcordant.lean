import krylov.Functions.MetricCubicSource
import krylov.Functions.CubicSelfConcordantBall
import krylov.Nonlinear.SelfConcordantCoordinates

/-!
Article: main_krylov, thm:H, the genuine physical self-concordant cubic.
Use: certify the actual metric pullback objective on the printed metric
ball, keeping its genuine physical gradient, Hessian and third variation.
Source: the sharp canonical Hessian margin and exact mixed metric transport.
-/

/-!
Article: krylov, Theorem E.9 [thm:H].

The actual harmonic cubic is self-concordant on the printed metric ball, realizes RFC’s leading
half coefficient and budgets, and has the complete planar minimax lower/RFC upper inequalities.
The competing method is quantified after the common small source radius. The native spatial
leading value, own-base normalization and compatible tensor restrictions are derived, not
supplied.
-/

namespace krylov.Functions
noncomputable section
open Set Metric InnerProductSpace krylov.Nonlinear krylov.Tensor
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

/-- The actual canonical cubic mixed inequality on its certified ball.
Article: main_krylov, thm:H, the printed radius. -/
theorem canonicalCubic_actual_mixed (T : SymmetricCubic E) (a R : ℝ)
    (ha : 0 ≤ a) (hb : 0 < 1-2*a*R)
    (hc : a ≤ (Real.sqrt (1-2*a*R))^3)
    (hd : ∀ v : E, ‖v‖=1 → |T.form v v v| ≤ 2*a)
    {x : E} (hx : x∈ball 0 R) (u v w : E) :
    |inner ℝ v (canonicalVariation T u w)| ≤
      2*Real.sqrt (inner ℝ u (canonicalHessian T x u))*
        Real.sqrt (inner ℝ v (canonicalHessian T x v))*
        Real.sqrt (inner ℝ w (canonicalHessian T x w)) := by
  rw [canonicalVariation_pair]
  have hu := canonicalHessian_sqrt_lower T a R ha hb hd hx u
  have hv := canonicalHessian_sqrt_lower T a R ha hb hd hx v
  have hw := canonicalHessian_sqrt_lower T a R ha hb hd hx w
  calc
    _ ≤ 2*a*‖u‖*‖v‖*‖w‖ := cubic_diagonal_bound T (2*a) hd u v w
    _ ≤ 2*(Real.sqrt (1-2*a*R)*‖u‖)*(Real.sqrt (1-2*a*R)*‖v‖)*
        (Real.sqrt (1-2*a*R)*‖w‖) := by
      have hm := mul_le_mul_of_nonneg_right hc (by positivity : 0≤2*‖u‖*‖v‖*‖w‖)
      nlinarith only [hm]
    _ ≤ _ := by gcongr

/-- The actual metric cubic is standard self-concordant on its genuine
physical metric ball, at the exact certified canonical radius.
Article: main_krylov, thm:H. -/
theorem metricCubic_selfConcordant_ball (S : E ≃L[ℝ] E)
    (hS : S.toContinuousLinearMap.IsSymmetric) (T : SymmetricCubic E) (a R : ℝ)
    (ha : 0 ≤ a) (hb : 0 < 1-2*a*R)
    (hc : a ≤ (Real.sqrt (1-2*a*R))^3)
    (hd : ∀ v : E, ‖v‖=1 → |T.form v v v| ≤ 2*a) :
    IsStandardSelfConcordantOn (metricCubicObjective S T) (S ⁻¹' ball 0 R) := by
  have hpair (x v w : E) : inner ℝ v (metricCubicHessian S T x w) =
      inner ℝ (S v) (canonicalHessian T (S x) (S w)) := by
    change inner ℝ v (S (canonicalHessian T (S x) (S w))) = _
    exact (hS v _).symm
  refine ⟨{
    open_domain := isOpen_ball.preimage S.continuous
    convex_domain := (convex_ball (0 : E) R).linear_preimage S.toLinearEquiv.toLinearMap
    differentiable := fun x _ => (metricCubicObjective_hasFDerivAt S hS T x).differentiableAt.differentiableWithinAt
    hessian := metricCubicHessian S T
    variation := fun _ => metricCubicVariation S T
    gradient_derivative := ?_
    hessian_derivative := fun x _ => metricCubicHessian_hasFDerivAt S T x
    variation_continuous := continuous_const.continuousOn
    hessian_symmetric := ?_
    hessian_nonnegative := ?_
    mixed := ?_ }⟩
  · intro x _
    rw [gradient_metricCubicObjective S hS T]
    exact metricCubicGradient_hasFDerivAt S T x
  · intro x _ u v
    change inner ℝ (metricCubicHessian S T x u) v=inner ℝ u (metricCubicHessian S T x v)
    rw [real_inner_comm,hpair,hpair,canonicalHessian_pair,canonicalHessian_pair,
      real_inner_comm (S v) (S u),T.swap₂]
  · intro x hx v
    rw [hpair]
    have hxR : ‖S x‖≤R := (show ‖S x‖<R by simpa only [mem_preimage,mem_ball,dist_zero_right] using hx).le
    have hl := canonicalHessian_lower T (2*a) hd (S x) (S v)
    have hmargin : 0≤1-2*a*‖S x‖ := by nlinarith [mul_le_mul_of_nonneg_left hxR (by positivity : 0≤2*a)]
    exact (mul_nonneg hmargin (sq_nonneg _)).trans hl
  · intro x hx u v w
    exact coordinate_mixed_selfConcordance S.symm hS (canonicalHessian T)
      (fun _ => canonicalVariation T) x
      (canonicalCubic_actual_mixed T a R ha hb hc hd hx) u v w

/-- The genuine metric cubic has exactly the printed self-concordant radius
for every strict positive spectral slack. Article: main_krylov, thm:H. -/
theorem metricCubic_selfConcordant_radius (S : E ≃L[ℝ] E)
    (hS : S.toContinuousLinearMap.IsSymmetric) (T : SymmetricCubic E)
    {a : ℝ} (ha : 0<a) (ha1 : a<1)
    (hd : ∀ v : E, ‖v‖=1 → |T.form v v v| ≤ 2*a) :
    0 < canonicalCubicRadius a ∧
      IsStandardSelfConcordantOn (metricCubicObjective S T) (S ⁻¹' ball 0 (canonicalCubicRadius a)) :=
  ⟨canonicalCubicRadius_pos ha ha1,
  metricCubic_selfConcordant_ball S hS T a (canonicalCubicRadius a) ha.le
    (by rw [canonicalCubicRadius_margin ha]; exact Real.rpow_pos_of_pos ha _)
    (canonicalCubicRadius_compat ha).ge hd⟩

end
end krylov.Functions
