import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
Article: main_krylov, Appendix C, apC:eq:f and apC:lem:fund.
Use: derive the Bellman identities from the differential equation of the
separating graph, without division by the graph velocity. This matters at the
interior saddle, where that velocity vanishes.
Source: elementary differentiation, with the square-root and power rules from
mathlib. Existence of the separating graph is a separate dynamical result.
-/

namespace krylov.ContinuumControl
noncomputable section

/-- The scalar Bellman candidate obtained from a positive separating graph.
Article: main_krylov, apC:eq:f. -/
def feedbackValue (γ : ℝ) (σ : ℝ → ℝ) (r : ℝ) : ℝ :=
  (r + σ r - 1) / (2 * γ * r * Real.sqrt (σ r))

/-- Polynomial cancellation behind the feedback derivative. The graph equation
is cross-multiplied, so the identity applies also at its stationary point.
Article: main_krylov, apC:lem:fund, first differentiation. -/
theorem feedback_derivative_algebra (γ r s t q : ℝ)
    (hγ : γ ≠ 0) (hr : r ≠ 0) (ht : t ≠ 0) (hts : t ^ 2 = s)
    (hgraph : r * q * (s + 1 - r) = 2 * s * (s - 1 - γ * r)) :
    ((1 + q) * (2 * γ * r * t) -
      (r + s - 1) * (2 * γ * t + 2 * γ * r * (q / (2 * t)))) /
      (2 * γ * r * t) ^ 2 = -1 / (2 * r * t) := by
  field_simp
  linear_combination hgraph + (2 * r * q - 2 * (s - 1 - γ * r)) * hts

/-- The derivative is forced by the graph ODE, even where its right-hand side
would have a zero denominator in solved form.
Article: main_krylov, apC:lem:fund, f' = −1/(2r√σ). -/
theorem hasDerivAt_feedbackValue {γ r q : ℝ} {σ : ℝ → ℝ}
    (hγ : γ ≠ 0) (hr : r ≠ 0) (hs : 0 < σ r)
    (hσ : HasDerivAt σ q r)
    (hgraph : r * q * (σ r + 1 - r) = 2 * σ r * (σ r - 1 - γ * r)) :
    HasDerivAt (feedbackValue γ σ) (-1 / (2 * r * Real.sqrt (σ r))) r := by
  have ht : Real.sqrt (σ r) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hs)
  have hd := (((hasDerivAt_id r).add hσ).sub_const 1).div
    ((((hasDerivAt_id r).const_mul (2 * γ)).mul (hσ.sqrt (ne_of_gt hs))))
    (mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hγ) hr) ht)
  convert hd using 1
  · rfl
  · simpa only [id_eq, Pi.mul_apply, Pi.add_apply, mul_one, one_mul] using
      (feedback_derivative_algebra γ r (σ r) (Real.sqrt (σ r)) q
        hγ hr ht (Real.sq_sqrt hs.le) hgraph).symm

/-- The second scalar Bellman identity uses only the defining formula and
positivity, after the derivative has been identified by the graph equation.
Article: main_krylov, apC:lem:fund. -/
theorem feedback_bellman (γ : ℝ) (σ : ℝ → ℝ) {r : ℝ}
    (hγ : γ ≠ 0) (hr : r ≠ 0) (hs : 0 < σ r) :
    (1 - r) * (-1 / (2 * r * Real.sqrt (σ r))) - γ * feedbackValue γ σ r =
      -Real.sqrt (σ r) / (2 * r) := by
  have ht : Real.sqrt (σ r) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hs)
  unfold feedbackValue
  field_simp
  linear_combination Real.sq_sqrt hs.le

/-- The Hamiltonian is the reward plus one explicit nonnegative square.
The optimum control is the square root of the separating graph.
Article: main_krylov, apC:eq:reduced and apC:lem:fund. -/
theorem feedback_hamiltonian (γ : ℝ) (σ : ℝ → ℝ) {r t : ℝ}
    (hγ : γ ≠ 0) (hr : r ≠ 0) (hs : 0 < σ r) (ht : t ≠ 0) :
    r / t * ((t ^ 2 + 1 - r) * (-1 / (2 * r * Real.sqrt (σ r))) -
      γ * feedbackValue γ σ r) =
      -1 - (t - Real.sqrt (σ r)) ^ 2 / (2 * t * Real.sqrt (σ r)) := by
  have hroot : Real.sqrt (σ r) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hs)
  have hb := feedback_bellman γ σ hγ hr hs
  calc
    _ = r / t * (t ^ 2 * (-1 / (2 * r * Real.sqrt (σ r))) -
        Real.sqrt (σ r) / (2 * r)) := by linear_combination (r / t) * hb
    _ = _ := by field_simp; ring

/-- Strict positivity of the terminal value on the invariant domain r ≥ 1.
Article: main_krylov, proof of thm:value. -/
theorem feedbackValue_pos {γ r : ℝ} {σ : ℝ → ℝ}
    (hγ : 0 < γ) (hr : 1 ≤ r) (hs : 0 < σ r) :
    0 < feedbackValue γ σ r := by
  apply div_pos
  · linarith
  · exact mul_pos (mul_pos (mul_pos (by norm_num) hγ) (lt_of_lt_of_le zero_lt_one hr))
      (Real.sqrt_pos.2 hs)

/-- The initial value depends only on the crossing of the separating graph.
Article: main_krylov, thm:value, Rγ = √sγ/(2γ). -/
theorem feedbackValue_one (γ : ℝ) (σ : ℝ → ℝ) (hs : 0 < σ 1) :
    feedbackValue γ σ 1 = Real.sqrt (σ 1) / (2 * γ) := by
  have ht : Real.sqrt (σ 1) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hs)
  unfold feedbackValue
  rw [show 1 + σ 1 - 1 = σ 1 by ring, mul_one]
  by_cases hγ : γ = 0
  · simp [hγ]
  · field_simp
    exact Real.sq_sqrt hs.le |>.symm

/- No existence or optimality of a separating graph is assumed in a structure:
every formula above is derived from its explicit graph differential equation. -/

end
end krylov.ContinuumControl
