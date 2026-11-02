import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Tactic

/-!
Article: main_krylov, thm:struct, gradient-indistinguishable cubic functions.
Use: construct actual scalar functions, differentiate them, and show exactly
which information is absent from sampled gradients and supplied by a value.
Source: the explicit polynomial construction in Appendix G of main_krylov.
-/

namespace krylov.Functions
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The univariate cubic with stationary endpoints and a nonzero value gap.
Article: main_krylov, thm:struct. -/
def hiddenPolynomial (t : ℝ) : ℝ := t ^ 3 / 6 - t ^ 2 / 4

/-- Its derivative is exactly t(t-1)/2.
Article: main_krylov, thm:struct.
Proof: differentiate the two monomials and normalize their coefficients. -/
theorem hiddenPolynomial_hasDerivAt (t : ℝ) :
    HasDerivAt hiddenPolynomial (t * (t - 1) / 2) t := by
  convert! (((hasDerivAt_id t).pow 3).div_const 6).sub
    (((hasDerivAt_id t).pow 2).div_const 4) using 1
  simp only [id_eq]
  ring

/-- The actual hidden cubic perturbation of a function in a linear coordinate.
Article: main_krylov, thm:struct. -/
def hiddenCubic (φ : E →L[ℝ] ℝ) (c : ℝ) (x₀ x : E) : ℝ :=
  c * hiddenPolynomial (φ (x - x₀))

/-- The hidden perturbation is smooth to every finite order.
Article: main_krylov, thm:struct. Proof: it is a polynomial in a continuous linear coordinate. -/
theorem hiddenCubic_contDiff (φ : E →L[ℝ] ℝ) (c : ℝ) (x₀ : E) (n : ℕ) :
    ContDiff ℝ n (hiddenCubic φ c x₀) := by
  unfold hiddenCubic hiddenPolynomial
  fun_prop

/-- The genuine Fréchet derivative of the hidden cubic.
Article: main_krylov, thm:struct.
Proof: compose the scalar polynomial derivative with the actual linear coordinate. -/
theorem hiddenCubic_hasFDerivAt (φ : E →L[ℝ] ℝ) (c : ℝ) (x₀ x : E) :
    HasFDerivAt (hiddenCubic φ c x₀)
      ((c * (φ (x - x₀) * (φ (x - x₀) - 1) / 2)) • φ) x := by
  have hφ : HasFDerivAt (fun y => φ (y - x₀)) φ x := by
    simpa only [Function.comp_def, ContinuousLinearMap.comp_id, id_eq] using!
      φ.hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const x₀)
  convert! ((hiddenPolynomial_hasDerivAt (φ (x - x₀))).comp_hasFDerivAt x hφ).const_mul c using 1
  ext y
  simp only [smul_apply, smul_eq_mul]
  ring

/-- At coordinate zero or one the perturbation has zero derivative.
Article: main_krylov, thm:struct. Proof: both scalar derivative factors vanish. -/
theorem hiddenCubic_hasFDerivAt_zero (φ : E →L[ℝ] ℝ) (c : ℝ) (x₀ x : E)
    (hx : φ (x - x₀) = 0 ∨ φ (x - x₀) = 1) :
    HasFDerivAt (hiddenCubic φ c x₀) (0 : E →L[ℝ] ℝ) x := by
  rcases hx with hx | hx <;> simpa [hx] using hiddenCubic_hasFDerivAt φ c x₀ x

/-- Adding the cubic preserves the actual derivative at every sampled point.
Use: an arbitrary base objective, in particular the article's quadratic, has identical gradient data.
Article: main_krylov, thm:struct. Proof: add a genuinely zero perturbation derivative. -/
theorem add_hiddenCubic_hasFDerivAt (f : E → ℝ) (f' : E →L[ℝ] ℝ)
    (φ : E →L[ℝ] ℝ) (c : ℝ) (x₀ x : E) (hf : HasFDerivAt f f' x)
    (hx : φ (x - x₀) = 0 ∨ φ (x - x₀) = 1) :
    HasFDerivAt (fun y => f y + hiddenCubic φ c x₀ y) f' x := by
  simpa only [Pi.add_apply, add_zero] using! hf.add (hiddenCubic_hasFDerivAt_zero φ c x₀ x hx)

/-- Duality with the first step makes all later observed coordinates equal to one.
Article: main_krylov, thm:struct, Sᵀφ=u₀.
Proof: telescope the true step recurrence; only the first step changes this coordinate. -/
theorem hidden_coordinate_of_steps (p : ℕ) (x s : ℕ → E) (φ : E →L[ℝ] ℝ)
    (hstep : ∀ i < p, x (i + 1) = x i + s i)
    (hφ : ∀ i < p, φ (s i) = if i = 0 then 1 else 0)
    {k : ℕ} (hk : k ≤ p) : φ (x k - x 0) = if k = 0 then 0 else 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hkp : k < p := by omega
    have he : x (k + 1) - x 0 = (x k - x 0) + s k := by rw [hstep k hkp]; abel
    rw [he, map_add, ih (by omega), hφ k hkp]
    by_cases hk₀ : k = 0 <;> simp [hk₀]

/-- Every derivative in the finite sampled transcript is unchanged by any coefficient c.
Article: main_krylov, thm:struct.
Proof: the proved coordinate recurrence puts every sample at a stationary scalar endpoint. -/
theorem hiddenCubic_sampled_derivative_zero (p : ℕ) (x s : ℕ → E) (φ : E →L[ℝ] ℝ)
    (hstep : ∀ i < p, x (i + 1) = x i + s i)
    (hφ : ∀ i < p, φ (s i) = if i = 0 then 1 else 0)
    (c : ℝ) {k : ℕ} (hk : k ≤ p) :
    HasFDerivAt (hiddenCubic φ c (x 0)) (0 : E →L[ℝ] ℝ) (x k) := by
  apply hiddenCubic_hasFDerivAt_zero
  rw [hidden_coordinate_of_steps p x s φ hstep hφ hk]
  split_ifs <;> simp

/-- The first function-value difference reveals exactly the previously hidden coefficient.
Article: main_krylov, thm:struct, oldest trapezoid defect.
Proof: evaluate the two cubic endpoints; their derivatives are both zero. -/
theorem hiddenCubic_endpoint_gap (φ : E →L[ℝ] ℝ) (c : ℝ) (x₀ s : E)
    (hs : φ s = 1) : hiddenCubic φ c x₀ (x₀ + s) - hiddenCubic φ c x₀ x₀ = -c / 12 := by
  simp only [hiddenCubic, hiddenPolynomial, add_sub_cancel_left, sub_self, map_zero, hs]
  ring

end
end krylov.Functions
