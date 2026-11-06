import nesterov.Flow.Constants
import polyak.Functions.Normalization
import polyak.Functions.Convexity

/-!
Article: §3, the class F_m and the heavy-ball equation.
Use: genuine Hilbert gradients, allowing gradients that are only Lipschitz on
bounded sets; no finite global smoothness constant is imposed on the class.
-/

noncomputable section

namespace nesterov.Flow

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The uncentered class F_m, using the equivalent first-order definition of
strong convexity, as in `polyak.SmoothStronglyConvex`. -/
structure StronglyConvexObjective (m : ℝ) (f : E → ℝ) : Prop where
  m_pos : 0 < m
  differentiable : Differentiable ℝ f
  tangent_lower : ∀ x y, f x + ⟪gradient f x, y - x⟫_ℝ +
    m / 2 * ‖y - x‖ ^ 2 ≤ f y
  gradient_lipschitz_bounded : ∀ R : ℝ, ∃ K : NNReal,
    LipschitzOnWith K (gradient f) (Metric.closedBall 0 R)

/-- The article's normalization of F_m: the minimizer and value are zero. -/
structure Objective (m : ℝ) (f : E → ℝ) : Prop
    extends StronglyConvexObjective m f where
  value_zero : f 0 = 0
  gradient_zero : gradient f 0 = 0

/-- Every globally smooth strongly convex objective belongs to F_m. -/
theorem of_smoothStronglyConvex {m L : ℝ} {f : E → ℝ}
    (hf : polyak.SmoothStronglyConvex m L f) : StronglyConvexObjective m f := by
  refine ⟨hf.mu_pos, hf.differentiable, hf.tangent_lower, fun _ => ?_⟩
  refine ⟨⟨L, by linarith [hf.mu_pos, hf.mu_lt_L]⟩, ?_⟩
  apply LipschitzWith.lipschitzOnWith
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change dist (gradient f x) (gradient f y) ≤ L * dist x y
  simpa only [dist_eq_norm] using hf.grad_lipschitz x y

theorem of_centeredSmoothStronglyConvex {m L : ℝ} {f : E → ℝ}
    (hf : polyak.CenteredSmoothStronglyConvex m L f) : Objective m f :=
  ⟨of_smoothStronglyConvex hf.toSmoothStronglyConvex, hf.value_zero, hf.gradient_zero⟩

/-- The convex remainder f_m. -/
def remainder (m : ℝ) (f : E → ℝ) (x : E) : ℝ := f x - m / 2 * ‖x‖ ^ 2

/-- The actual gradient of the convex remainder. -/
def remainderGradient (m : ℝ) (f : E → ℝ) (x : E) : E := gradient f x - m • x

theorem hasGradientAt_remainder {m : ℝ} {f : E → ℝ}
    (hf : Differentiable ℝ f) (x : E) :
    HasGradientAt (remainder m f) (remainderGradient m f x) x := by
  convert polyak.hasGradientAt_quadratic_add (hf x).hasGradientAt (-m) 1 using 1
  · funext y
    dsimp [remainder]
    ring
  · dsimp [remainderGradient]
    module

theorem StronglyConvexObjective.remainder_tangent {m : ℝ} {f : E → ℝ}
    (hf : StronglyConvexObjective m f) (x y : E) :
    remainder m f x + ⟪remainderGradient m f x, y - x⟫_ℝ ≤ remainder m f y := by
  have h := hf.tangent_lower x y
  dsimp [remainder, remainderGradient]
  simp only [inner_sub_left, inner_smul_left, norm_sub_sq_real, inner_sub_right,
    real_inner_self_eq_norm_sq, starRingEnd_apply, star_trivial] at h ⊢
  have hi : ⟪y, x⟫_ℝ = ⟪x, y⟫_ℝ := real_inner_comm x y
  rw [hi] at h
  nlinarith

omit [CompleteSpace E] in
/-- A global supporting gradient makes the represented function convex. -/
theorem convexOn_of_global_support {f : E → ℝ} {g : E → E}
    (h : ∀ x y, f x + ⟪g x, y - x⟫_ℝ ≤ f y) : ConvexOn ℝ Set.univ f := by
  exact polyak.convexOn_of_supporting_tangents h

/-- The first-order class definition gives exactly the convex remainder
used in the article, without any Hessian regularity requirement. -/
theorem StronglyConvexObjective.remainder_convex {m : ℝ} {f : E → ℝ}
    (hf : StronglyConvexObjective m f) : ConvexOn ℝ Set.univ (remainder m f) :=
  convexOn_of_global_support hf.remainder_tangent

/-- Exact identification with the article's definition of F_m: the convex
remainder and bounded-set Lipschitz gradient, with no global L assumption. -/
theorem stronglyConvexObjective_iff_standard {m : ℝ} {f : E → ℝ} :
    StronglyConvexObjective m f ↔ 0 < m ∧ Differentiable ℝ f ∧
      ConvexOn ℝ Set.univ (remainder m f) ∧
      ∀ R : ℝ, ∃ K : NNReal, LipschitzOnWith K (gradient f) (Metric.closedBall 0 R) := by
  constructor
  · intro hf
    exact ⟨hf.m_pos, hf.differentiable, hf.remainder_convex, hf.gradient_lipschitz_bounded⟩
  · rintro ⟨hm, hdiff, hconv, hlip⟩
    have hstrong : StrongConvexOn Set.univ m f := by
      rw [strongConvexOn_iff_convex]
      exact hconv
    exact ⟨hm, hdiff, (polyak.strongConvexOn_iff_tangent_lower hdiff).mp hstrong, hlip⟩

/-- Equation (hineq), the nonnegativity of f_m. -/
theorem Objective.remainder_nonneg {m : ℝ} {f : E → ℝ} (hf : Objective m f)
    (x : E) : 0 ≤ remainder m f x := by
  have h := hf.toStronglyConvexObjective.remainder_tangent 0 x
  simpa [remainder, remainderGradient, hf.value_zero, hf.gradient_zero] using h

/-- Equation (hineq), convexity between the current point and the minimizer. -/
theorem Objective.remainder_support_nonneg {m : ℝ} {f : E → ℝ}
    (hf : Objective m f) (x : E) :
    0 ≤ ⟪remainderGradient m f x, x⟫_ℝ - remainder m f x := by
  have h := hf.toStronglyConvexObjective.remainder_tangent x 0
  simp only [zero_sub, inner_neg_right] at h
  have hz : remainder m f 0 = 0 := by simp [remainder, hf.value_zero]
  rw [hz] at h
  linarith

theorem Objective.quadratic_lower {m : ℝ} {f : E → ℝ} (hf : Objective m f)
    (x : E) : m / 2 * ‖x‖ ^ 2 ≤ f x := by
  have h := hf.remainder_nonneg x
  dsimp [remainder] at h
  linarith

theorem Objective.minimizer_unique {m : ℝ} {f : E → ℝ} (hf : Objective m f)
    {x : E} (hx : f x ≤ f 0) : x = 0 := by
  have h := hf.quadratic_lower x
  rw [hf.value_zero] at hx
  have hz : ‖x‖ = 0 := by
    by_contra hn
    have hn' : 0 < ‖x‖ := (norm_nonneg x).lt_of_ne' hn
    have hp := mul_pos (show 0 < m / 2 by linarith [hf.m_pos]) (sq_pos_of_pos hn')
    linarith
  exact norm_eq_zero.mp hz

/-- A solution on the nonnegative half-line, with its actual velocity.  Full
derivatives at the endpoint permit the usual local extension about time zero. -/
structure IsSolution (θ : ℝ) (f : E → ℝ) (x v : ℝ → E) : Prop where
  position_derivative : ∀ t, 0 ≤ t → HasDerivAt x (v t) t
  velocity_derivative : ∀ t, 0 ≤ t →
    HasDerivAt v (-θ • v t - gradient f (x t)) t

/-- The autonomous first-order vector field equivalent to the heavy-ball equation. -/
def vectorField (θ : ℝ) (f : E → ℝ) (z : E × E) : E × E :=
  (z.2, -θ • z.2 - gradient f z.1)

/-- Mechanical energy, normalized by f(0)=0. -/
def energy (f : E → ℝ) (x v : E) : ℝ := f x + ‖v‖ ^ 2 / 2

/-- The Lyapunov potential of Theorem flow(a), in its coercive form. -/
def lyapunov (θ m c : ℝ) (f : E → ℝ) (x v : E) : ℝ :=
  remainder m f x + delta θ m c / 2 * ‖x‖ ^ 2 + ‖v + (θ - c) • x‖ ^ 2 / 2

omit [CompleteSpace E] in
theorem lyapunov_eq_original (θ m c : ℝ) (f : E → ℝ) (x v : E) :
    lyapunov θ m c f x v =
      f x - c * (θ - c) / 2 * ‖x‖ ^ 2 + ‖v + (θ - c) • x‖ ^ 2 / 2 := by
  dsimp [lyapunov, remainder, delta]
  ring

end nesterov.Flow
