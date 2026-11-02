import krylov.Functions.CubicSelfConcordant

/-!
Article: main_krylov, thm:H, cubic functions on a certified self-concordant ball.
Use: prove the full standard mixed self-concordance condition for actual
scalar cubic functions, with the stated sharp radius. Source: the true
Hessian lower bound, Banach's proved cubic identity, and exact power algebra.
-/

namespace krylov.Functions
noncomputable section
open InnerProductSpace krylov.Tensor krylov.Nonlinear
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

/-- The true Hessian is bounded below directly by the tensor's diagonal norm.
Article: main_krylov, thm:H, I+T[x] >= (1-c*norm x)I. -/
theorem canonicalHessian_lower (T : SymmetricCubic E) (c : ℝ)
    (hdiag : ∀ u : E, ‖u‖=1 → |T.form u u u|≤c) (x v : E) :
    (1-c*‖x‖)*‖v‖^2≤ inner ℝ v (canonicalHessian T x v) := by
  have h := (abs_le.mp (cubic_diagonal_bound T c hdiag x v v)).1
  rw [canonicalHessian_pair,real_inner_self_eq_norm_sq]
  nlinarith

/-- On a certified ball the actual Hessian square roots dominate the uniform
Euclidean lower metric. Article: main_krylov, thm:H. -/
theorem canonicalHessian_sqrt_lower (T : SymmetricCubic E) (a R : ℝ) (ha : 0≤a)
    (hb : 0<1-2*a*R)
    (hdiag : ∀ u : E, ‖u‖=1 → |T.form u u u|≤2*a)
    {x : E} (hx : x∈Metric.ball 0 R) (v : E) :
    Real.sqrt (1-2*a*R)*‖v‖≤Real.sqrt (inner ℝ v (canonicalHessian T x v)) := by
  have hxR : ‖x‖≤R := (show ‖x‖<R by simpa [Metric.mem_ball,dist_zero_right] using hx).le
  have hlow := canonicalHessian_lower T (2*a) hdiag x v
  have hcomp : (1-2*a*R)*‖v‖^2≤ inner ℝ v (canonicalHessian T x v) := by
    nlinarith [mul_nonneg (mul_nonneg (by positivity : 0≤2*a) (sub_nonneg.mpr hxR)) (sq_nonneg ‖v‖)]
  have hnonneg : 0≤ inner ℝ v (canonicalHessian T x v) :=
    (mul_nonneg hb.le (sq_nonneg _)).trans hcomp
  apply (sq_le_sq₀ (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)) (Real.sqrt_nonneg _)).mp
  rw [mul_pow,Real.sq_sqrt hb.le,Real.sq_sqrt hnonneg]
  exact hcomp

/-- The full actual cubic scalar function is standard self-concordant on a
ball whenever the tensor budget fits its true uniform Hessian metric.
Article: main_krylov, thm:H.
Proof: all differential fields are the proved genuine derivatives. Banach
bounds the third variation, while the Hessian lower metric pays its three
norm factors. -/
theorem canonicalCubic_selfConcordant_ball (T : SymmetricCubic E) (a R : ℝ)
    (ha : 0≤a) (hb : 0<1-2*a*R)
    (hcompat : a≤(Real.sqrt (1-2*a*R))^3)
    (hdiag : ∀ u : E, ‖u‖=1 → |T.form u u u|≤2*a) :
    IsStandardSelfConcordantOn (canonicalCubic T) (Metric.ball 0 R) := by
  refine ⟨{
    open_domain := Metric.isOpen_ball
    convex_domain := convex_ball 0 R
    differentiable := fun x _ => (canonicalCubic_hasFDerivAt T x).differentiableAt.differentiableWithinAt
    hessian := canonicalHessian T
    variation := fun _ => canonicalVariation T
    gradient_derivative := ?_
    hessian_derivative := fun x _ => canonicalHessian_hasFDerivAt T x
    variation_continuous := continuous_const.continuousOn
    hessian_symmetric := ?_
    hessian_nonnegative := ?_
    mixed := ?_ }⟩
  · intro x _
    rw [gradient_canonicalCubic]
    exact canonicalGradient_hasFDerivAt T x
  · intro x _ u v
    change inner ℝ (canonicalHessian T x u) v=inner ℝ u (canonicalHessian T x v)
    rw [real_inner_comm v (canonicalHessian T x u),canonicalHessian_pair,
      canonicalHessian_pair,real_inner_comm u v,T.swap₂ x v u]
  · intro x hx v
    have hxR : ‖x‖≤R := (show ‖x‖<R by simpa [Metric.mem_ball,dist_zero_right] using hx).le
    have hlow := canonicalHessian_lower T (2*a) hdiag x v
    have hpos : 0≤1-2*a*‖x‖ := by nlinarith [mul_le_mul_of_nonneg_left hxR (by positivity : 0≤2*a)]
    exact (mul_nonneg hpos (sq_nonneg _)).trans hlow
  · intro x hx u v w
    rw [canonicalVariation_pair]
    have hu := canonicalHessian_sqrt_lower T a R ha hb hdiag hx u
    have hv := canonicalHessian_sqrt_lower T a R ha hb hdiag hx v
    have hw := canonicalHessian_sqrt_lower T a R ha hb hdiag hx w
    have hT := cubic_diagonal_bound T (2*a) hdiag u v w
    calc
      |T.form u v w| ≤ 2*a*‖u‖*‖v‖*‖w‖ := hT
      _ ≤ 2*(Real.sqrt (1-2*a*R)*‖u‖)*(Real.sqrt (1-2*a*R)*‖v‖)*
          (Real.sqrt (1-2*a*R)*‖w‖) := by
        have h := mul_le_mul_of_nonneg_right hcompat (by positivity : 0≤2*‖u‖*‖v‖*‖w‖)
        nlinarith
      _ ≤ 2*Real.sqrt (inner ℝ u (canonicalHessian T x u))*
          Real.sqrt (inner ℝ v (canonicalHessian T x v))*
          Real.sqrt (inner ℝ w (canonicalHessian T x w)) := by
        gcongr

/-- The explicit radius associated with a strict canonical cubic budget.
Article: main_krylov, thm:H, a=1-delta. -/
def canonicalCubicRadius (a : ℝ) : ℝ := (1-a^((2:ℝ)/3))/(2*a)

/-- The exact Hessian margin at the printed radius.
Article: main_krylov, thm:H. -/
theorem canonicalCubicRadius_margin {a : ℝ} (ha : 0<a) :
    1-2*a*canonicalCubicRadius a=a^((2:ℝ)/3) := by
  unfold canonicalCubicRadius
  field_simp
  ring

/-- The square-root metric at the printed radius exactly pays the cubic budget.
Article: main_krylov, thm:H. -/
theorem canonicalCubicRadius_compat {a : ℝ} (ha : 0<a) :
    (Real.sqrt (1-2*a*canonicalCubicRadius a))^3=a := by
  rw [canonicalCubicRadius_margin ha,Real.sqrt_eq_rpow]
  rw [← Real.rpow_natCast,← Real.rpow_mul (Real.rpow_nonneg ha.le _),← Real.rpow_mul ha.le]
  norm_num

/-- The printed radius is strictly positive for every strict positive budget.
Article: main_krylov, thm:H, 0<delta<1. -/
theorem canonicalCubicRadius_pos {a : ℝ} (ha : 0<a) (ha1 : a<1) :
    0<canonicalCubicRadius a := by
  apply div_pos
  · exact sub_pos.mpr (Real.rpow_lt_one ha.le ha1 (by norm_num))
  · positivity

/-- The actual canonical cubic is self-concordant on exactly the stated ball
for every tensor within the strict diagonal budget.
Article: main_krylov, thm:H, the self-concordant cubic realization.
Proof: the printed radius gives Hessian margin a^(2/3), whose square-root
cube equals a; the general actual-function theorem then applies. -/
theorem canonicalCubic_selfConcordant_radius (T : SymmetricCubic E) {a : ℝ} (ha : 0<a)
    (hdiag : ∀ u : E, ‖u‖=1 → |T.form u u u|≤2*a) :
    IsStandardSelfConcordantOn (canonicalCubic T) (Metric.ball 0 (canonicalCubicRadius a)) := by
  apply canonicalCubic_selfConcordant_ball T a (canonicalCubicRadius a) ha.le
  · rw [canonicalCubicRadius_margin ha]
    exact Real.rpow_pos_of_pos ha _
  · exact (canonicalCubicRadius_compat ha).ge
  · exact hdiag

end
end krylov.Functions
