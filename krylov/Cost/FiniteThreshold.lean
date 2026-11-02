import krylov.Cost.CriticalTolerance
import krylov.Asymptotics.DesignUpperBound

/-!
Article: main_krylov, thm:limit special exponents and cor:threshold.
Use: the exact printed half-power and energy-power constants apply to
the original finite design optima. Inverting the true half-power bound
gives the actual uniform FC tolerance lower bound.
Source: the proved general finite-string/design estimate.
-/

namespace krylov.Asymptotics
noncomputable section
open Real krylov.Design krylov.ContinuumControl

/-- The literal half-power specialization retains the source constants
three eighths and three halves. -/
theorem finiteDesignUpper_half (I : chebyshev1.SpectralInterval) (σ : ℝ → ℝ) (hs : 0 < σ 1) :
    finiteDesignUpper I (1 / 2) (1 / 2) σ =
      sqrt (σ 1) / 2 * sqrt (I.kappa - 1) + 3 / 8 * log I.kappa + 3 / 2 := by
  rw [finiteDesignUpper, feedbackValue_one _ _ hs]
  norm_num
  ring

/-- The literal energy-power specialization used by the sharp total
Hilbert--Schmidt response has additive constant one. -/
theorem finiteDesignUpper_one (I : chebyshev1.SpectralInterval) (σ : ℝ → ℝ) (hs : 0 < σ 1) :
    finiteDesignUpper I 1 (1 / 2) σ =
      sqrt (σ 1) / 4 * sqrt (I.kappa - 1) + 3 / 8 * log I.kappa + 1 := by
  rw [finiteDesignUpper, feedbackValue_one _ _ hs]
  norm_num
  ring

/-- The exact source finite-cycle half-power estimate. -/
theorem optimalValue_half_sharp_upper (I : chebyshev1.SpectralInterval) (M : ℕ)
    {σ : ℝ → ℝ} (hgraph : ∀ r ≥ 1, FeedbackGraphAt (1 / 2) σ r)
    (hlog : ∀ r ≥ 1, 0 ≤ logSlope σ r ∧ logSlope σ r ≤ 1 / 2) :
    optimalValue I M (fun _ ↦ 1) (1 / 2) ≤
      sqrt (σ 1) / 2 * sqrt (I.kappa - 1) + 3 / 8 * log I.kappa + 3 / 2 := by
  simpa only [finiteDesignUpper_half I σ (hgraph 1 le_rfl).positive] using
    optimalValue_sharp_upper I M (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (1 / 2 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) ≤ 1 / 2) hgraph hlog

end
end krylov.Asymptotics

namespace krylov.Cost
noncomputable section
open Real krylov.Design krylov.ContinuumControl krylov.Asymptotics

/-- The displayed source lower bound on the actual FC critical tolerance,
with no assumed optimized-value estimate. -/
theorem criticalTolerance_half_lower (I : chebyshev1.SpectralInterval) {M : ℕ} (hM : 0 < M)
    {σ : ℝ → ℝ} (hgraph : ∀ r ≥ 1, FeedbackGraphAt (1 / 2) σ r)
    (hlog : ∀ r ≥ 1, 0 ≤ logSlope σ r ∧ logSlope σ r ≤ 1 / 2) :
    (sqrt (σ 1) / 2 * sqrt (I.kappa - 1) + 3 / 8 * log I.kappa + 3 / 2)⁻¹ ≤
      criticalTolerance I M :=
  criticalTolerance_ge_of_upper I hM (optimalValue_half_sharp_upper I M hgraph hlog)

end
end krylov.Cost
