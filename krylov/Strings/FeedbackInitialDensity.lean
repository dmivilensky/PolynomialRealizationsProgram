import krylov.Strings.FeedbackAlgebra
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
Article: main_krylov, thm:value, M*'(0+) = sγ⁻¹.
Use: identify the exact initial physical density once the positive crossing
has been constructed. The crossing itself is not numerically assumed.
Source: unit state initialization and the positive square-root identity.
-/

namespace krylov.Strings
noncomputable section

/-- The feedback mass density at the unit state is the reciprocal crossing. -/
theorem feedback_initial_mass_density {s : ℝ} (hs : 0 < s) :
    feedbackDensity 1 1 (Real.sqrt s) ^ 2 = s⁻¹ := by
  rw [feedbackDensity_initial, inv_pow, Real.sq_sqrt hs.le]

/-- Writing a=√s turns the same exact density into a⁻². -/
theorem feedback_initial_density_value {s a : ℝ} (hs : 0 < s)
    (ha : a ^ 2 = s) :
    feedbackDensity 1 1 (Real.sqrt s) ^ 2 = 1 / a ^ 2 := by
  rw [feedback_initial_mass_density hs, ha, one_div]

end
end krylov.Strings
