import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

/-!
Article: main_krylov, thm:limit, final upper-bound cancellation.
Use: combine the actual bond/site estimate, weighted Abel bound and energy
logarithm budget without losing any of the printed finite constants.
Source: the displayed finite-sum calculation in the article's upper proof.
-/

namespace krylov.Asymptotics
noncomputable section

/-- The exact finite-sum cancellation giving all four printed upper terms.
The hypotheses are the scalar outputs of the actual string estimates. -/
theorem finite_bound_algebra {S D K Q W Λ a B γ g₀ : ℝ}
    (hB : 0 ≤ B) (hg : g₀ ≤ 1) (hW : W ≤ a)
    (hpair : 4 * S - 2 * g₀ - ((1 + B) * D + B * K + (1 - B) * Q) ≤
      2 * Real.sqrt Λ * W)
    (hAbel : D ≤ Real.log (1 + Λ) + K - Q) (hQ : 0 ≤ Q) (hK : K ≤ 1 / γ) :
    S ≤ Real.sqrt Λ * a / 2 + (1 + B) / 4 * Real.log (1 + Λ) +
      1 / 2 + (1 + 2 * B) / (4 * γ) := by
  have hD := mul_le_mul_of_nonneg_left hAbel (by linarith : 0 ≤ 1 + B)
  have hbudget := mul_le_mul_of_nonneg_left hK (by linarith : 0 ≤ 1 + 2 * B)
  have hnonneg : 0 ≤ 2 * B * Q := mul_nonneg (by positivity) hQ
  have hbracket : (1 + B) * D + B * K + (1 - B) * Q ≤
      (1 + B) * Real.log (1 + Λ) + (1 + 2 * B) / γ := by
    have he : (1 + 2 * B) * (1 / γ) = (1 + 2 * B) / γ := by ring
    rw [he] at hbudget
    nlinarith
  have hvalue := mul_le_mul_of_nonneg_left hW
    (mul_nonneg (show (0 : ℝ) ≤ 2 by norm_num) (Real.sqrt_nonneg Λ))
  have he : (1 + 2 * B) / (4 * γ) = ((1 + 2 * B) / γ) / 4 := by ring
  rw [he]
  nlinarith

end
end krylov.Asymptotics
