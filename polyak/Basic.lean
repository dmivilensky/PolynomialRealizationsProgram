import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Convex.Strong

/-!
Article: polyaksiopt, §1 and Lemma `normalization`.
Use: genuine differentiable functions and their actual Hilbert gradients.
-/

namespace polyak

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Article: the normalized class S. Use: interpolation and normalized dynamics.
The gradient here is the actual derivative represented by the Hilbert inner product. -/
structure NormalizedSmooth (ψ : E → ℝ) : Prop where
  /-- Article: differentiability, without a second derivative assumption. -/
  differentiable : Differentiable ℝ ψ
  /-- Article: gradient Lipschitz constant at most one. -/
  grad_lipschitz : LipschitzWith 1 (gradient ψ)
  /-- Article: the normalized function value. -/
  value_zero : ψ 0 = 0
  /-- Article: the prescribed stationary point. -/
  gradient_zero : gradient ψ 0 = 0

/-- Article: the original smooth strongly convex class.
Use: a lower first-order inequality is the differentiable characterization of
strong convexity; no assumption on a Hessian or normalized gradient is made. -/
structure SmoothStronglyConvex (μ L : ℝ) (f : E → ℝ) : Prop where
  /-- Article: strong convexity parameter. -/
  mu_pos : 0 < μ
  /-- Article: the nondegenerate condition number range. -/
  mu_lt_L : μ < L
  /-- Article: genuine differentiability. -/
  differentiable : Differentiable ℝ f
  /-- Article: μ-strong convexity in its first-order formulation. -/
  tangent_lower : ∀ x y, f x + inner (𝕜 := ℝ) (gradient f x) (y - x) +
    μ / 2 * ‖y - x‖ ^ 2 ≤ f y
  /-- Article: smoothness of the actual gradient. -/
  grad_lipschitz : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖

/-- Article: f has minimizer zero and value zero there. Use: normalization's domain. -/
structure CenteredSmoothStronglyConvex (μ L : ℝ) (f : E → ℝ) : Prop
    extends SmoothStronglyConvex μ L f where
  /-- Article: value normalization. -/
  value_zero : f 0 = 0
  /-- Article: the actual stationary point is the origin. -/
  gradient_zero : gradient f 0 = 0

end polyak
