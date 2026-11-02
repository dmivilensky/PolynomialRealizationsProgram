import krylov.Strings.FeedbackFlow
import krylov.Strings.FeedbackInvariant
import krylov.ContinuumControl.SmoothIdentity

/-!
Article: main_krylov, thm:value, physical feedback construction.
Use: connect the actual Picard–Lindelöf solution to the physical string
equations used by the Bellman identity. A positive C¹ graph is enough for
this local construction; proving the separating graph is a separate result.
Source: coordinate differentiation and `feedback_physical_rates`.
-/

namespace krylov.Strings
noncomputable section
open Set

/-- The genuine density along a physical feedback trajectory. -/
def feedbackCurveDensity (σ : ℝ → ℝ) (α : ℝ → FeedbackState) (x : ℝ) : ℝ :=
  feedbackDensity (α x).1 (α x).2.1
    (Real.sqrt (σ (stateRatio (α x).1 (α x).2.1 (α x).2.2)))

/-- Every positive solution of the closed-loop ODE is an actual smooth
string state, with its computed density rather than a supplied control. -/
theorem feedback_solution_smoothStringAt {σ : ℝ → ℝ} {α : ℝ → FeedbackState} {x : ℝ}
    (hd : HasDerivAt α (feedbackField σ (α x)) x)
    (hφ : 0 < (α x).1) (hp : 0 < (α x).2.1) (hK : 0 < (α x).2.2)
    (hσ : 0 < σ (stateRatio (α x).1 (α x).2.1 (α x).2.2)) :
    krylov.ContinuumControl.SmoothStringAt
      (fun u ↦ (α u).1) (fun u ↦ (α u).2.1) (fun u ↦ (α u).2.2)
      (feedbackCurveDensity σ α) x := by
  have ht : Real.sqrt (σ (stateRatio (α x).1 (α x).2.1 (α x).2.2)) ≠ 0 :=
    (Real.sqrt_pos.mpr hσ).ne'
  obtain ⟨hrp, hrK⟩ := feedback_physical_rates (α x).1 (α x).2.1
    (Real.sqrt (σ (stateRatio (α x).1 (α x).2.1 (α x).2.2)))
    (σ (stateRatio (α x).1 (α x).2.1 (α x).2.2)) hφ.ne' ht
    (Real.sq_sqrt hσ.le)
  refine ⟨hφ, hp, hK, ?_, ?_, ?_⟩
  · convert (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)).hasFDerivAt.comp_hasDerivAt x hd using 1
    all_goals rfl
  · have h := hd.snd.fst
    change HasDerivAt (fun u ↦ (α u).2.1)
      ((α x).2.1 ^ 2 / ((α x).1 * σ (stateRatio (α x).1 (α x).2.1 (α x).2.2))) x at h
    rw [← hrp] at h
    simpa only [feedbackCurveDensity, mul_comm] using h
  · have h := hd.snd.snd
    change HasDerivAt (fun u ↦ (α u).2.2)
      ((α x).2.1 ^ 2 / σ (stateRatio (α x).1 (α x).2.1 (α x).2.2)) x at h
    rw [← hrK] at h
    simpa only [feedbackCurveDensity, mul_comm] using h

/-- Local existence in the exact physical string variables and equations.
The positive solution has no separately assumed derivative identities. -/
theorem exists_local_feedback_string {σ : ℝ → ℝ}
    (hσ : ContDiffAt ℝ 1 σ 1) (hσpos : 0 < σ 1) :
    ∃ α : ℝ → FeedbackState, α 0 = (1, 1, 1) ∧ ∃ ε > (0 : ℝ),
      ∀ x ∈ Ioo (-ε) ε,
        krylov.ContinuumControl.SmoothStringAt
          (fun u ↦ (α u).1) (fun u ↦ (α u).2.1) (fun u ↦ (α u).2.2)
          (feedbackCurveDensity σ α) x := by
  obtain ⟨α, hα, ε, hε, hd⟩ := feedback_local_positive_solution hσ hσpos
  refine ⟨α, hα, ε, hε, ?_⟩
  intro x hx
  obtain ⟨hode, hφ, hp, hK, hs⟩ := hd x hx
  exact feedback_solution_smoothStringAt hode hφ hp hK hs

end
end krylov.Strings
