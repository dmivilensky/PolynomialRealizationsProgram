import krylov.Strings.FeedbackAlgebra
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
Article: main_krylov, apC:sec:value, invariant φp/K ≥ 1.
Use: establish the physical invariant for genuinely differentiable states.
The corresponding arbitrary-measure BV identity is a separate obligation.
Source: the mass terms cancel in d(φp−K); apply the mean value theorem.
-/

namespace krylov.Strings
noncomputable section
open Set

/-- A physical continuous-density string has nondecreasing excess φp−K,
independently of its choice of feedback or control. -/
theorem smooth_state_excess_monotone {φ p K v : ℝ → ℝ} {a b : ℝ}
    (hφ : ∀ x ∈ Icc a b, HasDerivAt φ (p x) x)
    (hp : ∀ x ∈ Icc a b, HasDerivAt p (v x ^ 2 * φ x) x)
    (hK : ∀ x ∈ Icc a b, HasDerivAt K (v x ^ 2 * φ x ^ 2) x) :
    MonotoneOn (fun x ↦ φ x * p x - K x) (Icc a b) := by
  have hd : ∀ x ∈ Icc a b,
      HasDerivAt (fun u ↦ φ u * p u - K u) (p x ^ 2) x := by
    intro x hx
    exact state_excess_derivative (hφ x hx) (hp x hx) (hK x hx)
  exact monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc a b)
    (fun x hx ↦ (hd x hx).continuousAt.continuousWithinAt)
    (fun x hx ↦ (hd x (interior_subset hx)).hasDerivWithinAt)
    (fun x _ ↦ sq_nonneg (p x))

/-- The unit initial state places every smooth physical state in the
domain on which the Bellman candidate is positive. -/
theorem smooth_state_ratio_ge_one {φ p K v : ℝ → ℝ} {b x : ℝ}
    (hx : x ∈ Icc 0 b)
    (hφ : ∀ u ∈ Icc 0 b, HasDerivAt φ (p u) u)
    (hp : ∀ u ∈ Icc 0 b, HasDerivAt p (v u ^ 2 * φ u) u)
    (hK : ∀ u ∈ Icc 0 b, HasDerivAt K (v u ^ 2 * φ u ^ 2) u)
    (hinit : φ 0 * p 0 = K 0) (hKpos : 0 < K x) :
    1 ≤ stateRatio (φ x) (p x) (K x) := by
  have hm := smooth_state_excess_monotone hφ hp hK
  have he := hm (show (0 : ℝ) ∈ Icc 0 b from ⟨le_rfl, hx.1.trans hx.2⟩) hx hx.1
  dsimp [stateRatio]
  apply (le_div_iff₀ hKpos).2
  dsimp only at he
  rw [hinit] at he
  linarith

end
end krylov.Strings
