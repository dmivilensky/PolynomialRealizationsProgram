import krylov.Functions.HiddenHessian
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Basis

/-!
Article: main_krylov, thm:struct, exact gradient data and compressed hidden curvature.
Use: connect the scalar construction to actual Riesz gradients and window matrices;
retain both the information obstruction and its recovery from a function value.
Source: explicit cubic family in Appendix G; all differentiation is proved upstream.
-/

namespace krylov.Functions
noncomputable section
open Matrix
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Compress an actual continuous bilinear form to the observed step columns.
Article: main_krylov, thm:struct. -/
def compressBilinear {p : ℕ} (s : Fin p → E) (B : E →L[ℝ] E →L[ℝ] ℝ) :
    Matrix (Fin p) (Fin p) ℝ := fun i j => B (s i) (s j)

/-- The hidden coordinate compresses to exactly one window diagonal entry.
Article: main_krylov, thm:struct, Sᵀ phi phiᵀ S=u₀u₀ᵀ.
Proof: evaluate the genuine bilinear form on the dual step columns. -/
theorem compress_coordinateSquare {p : ℕ} (s : Fin p → E) (i₀ : Fin p)
    (φ : E →L[ℝ] ℝ) (hφ : ∀ i, φ (s i) = if i = i₀ then 1 else 0) :
    compressBilinear s (coordinateSquare φ) = Matrix.single i₀ i₀ 1 := by
  ext i j
  simp only [compressBilinear, coordinateSquare, ContinuousLinearMap.smulRight_apply,
    hφ, Matrix.single]
  split_ifs <;> simp_all [eq_comm]

/-- The coordinate of an arbitrary window correction is exactly its hidden coefficient.
Article: main_krylov, thm:struct, phiᵀSw=w₀.
Proof: apply the genuine linear functional to the actual finite correction sum. -/
theorem coordinate_window_correction {p : ℕ} (s : Fin p → E) (i₀ : Fin p)
    (φ : E →L[ℝ] ℝ) (hφ : ∀ i, φ (s i) = if i = i₀ then 1 else 0) (w : Fin p → ℝ) :
    φ (∑ i, w i • s i) = w i₀ := by
  simp [map_sum, hφ, smul_eq_mul]

/-- The actual final secant has the source's exact rank-one compressed drift.
Article: main_krylov, thm:struct.
Proof: combine the genuine correction midpoint integral with the exact dual coordinate. -/
theorem hidden_correction_compression {p : ℕ} (s : Fin p → E) (i₀ : Fin p)
    (φ : E →L[ℝ] ℝ) (hφ : ∀ i, φ (s i) = if i = i₀ then 1 else 0)
    (c : ℝ) (x₀ a : E) (ha : φ (a - x₀) = 1) (w : Fin p → ℝ) :
    compressBilinear s
      (chebyshev1.Nonlinear.averagedDerivative (hiddenHessian φ c x₀) a (∑ i, w i • s i)) =
      (c / 2 * (1 + w i₀)) • Matrix.single i₀ i₀ 1 := by
  rw [hidden_correction_secant φ c x₀ a _ ha, coordinate_window_correction s i₀ φ hφ w]
  have h := compress_coordinateSquare s i₀ φ hφ
  ext i j
  exact congrArg (fun B : Matrix (Fin p) (Fin p) ℝ => (c / 2 * (1 + w i₀)) * B i j) h


end

section Gradient
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The actual Riesz gradients agree at every observed stationary coordinate.
Article: main_krylov, thm:struct.
Proof: both genuine Frechet derivatives equal the same base derivative, then apply the Riesz inverse. -/
theorem add_hiddenCubic_gradient (f : E → ℝ) (f' : E →L[ℝ] ℝ)
    (φ : E →L[ℝ] ℝ) (c : ℝ) (x₀ x : E) (hf : HasFDerivAt f f' x)
    (hx : φ (x - x₀) = 0 ∨ φ (x - x₀) = 1) :
    gradient (fun y => f y + hiddenCubic φ c x₀ y) x = gradient f x := by
  unfold gradient
  rw [(add_hiddenCubic_hasFDerivAt f f' φ c x₀ x hf hx).fderiv, hf.fderiv]

/-- The whole finite gradient transcript is exactly independent of the hidden parameter.
Article: main_krylov, thm:struct.
Proof: use the proved actual step-coordinate recurrence and genuine Riesz derivative identity. -/
theorem hiddenCubic_gradient_transcript (p : ℕ) (x s : ℕ → E) (φ : E →L[ℝ] ℝ)
    (hstep : ∀ i < p, x (i + 1) = x i + s i)
    (hφ : ∀ i < p, φ (s i) = if i = 0 then 1 else 0)
    (f : E → ℝ) (hf : ∀ k ≤ p, DifferentiableAt ℝ f (x k)) (c : ℝ) :
    ∀ k ≤ p, gradient (fun y => f y + hiddenCubic φ c (x 0) y) (x k) = gradient f (x k) := by
  intro k hk
  apply add_hiddenCubic_gradient f _ φ c (x 0) (x k) (hf k hk).hasFDerivAt
  rw [hidden_coordinate_of_steps p x s φ hstep hφ hk]
  split_ifs <;> simp

end Gradient
end krylov.Functions
