import krylov.ContinuumControl.Maximum
import krylov.Strings.OptimizerUniqueness

/-!
Article: main_krylov, thm:value, the attained unique continuum maximum.
Use: remove monotonicity and smoothness from the uniqueness hypotheses:
the original continuous Volterra state equation alone suffices. Combine
actual global attainment with the proved necessity of feedback and mass
uniqueness to obtain the unique actual maximizing string for all 0<gamma≤1.
Source: the canonical actual state and the full BV equality analysis.
-/

namespace krylov.Strings
noncomputable section
open Set Filter MeasureTheory
open krylov.ContinuumControl
open scoped Topology

/-- Original admissibility and equality in the sharp bound determine the
actual mass uniquely. Monotonicity is obtained from the canonical state. -/
theorem IsState.mass_unique_of_optimal_reward {M N : Mass} {φ ψ σ : ℝ → ℝ} {γ : ℝ}
    (hM : IsState M φ) (hN : IsState N ψ) (hγ : 0 < γ)
    (hσ : ∀ r ≥ 1, ContDiffAt ℝ 1 σ r) (hgraph : ∀ r ≥ 1, FeedbackGraphAt γ σ r)
    (hoptM : M.reward γ φ = ENNReal.ofReal (feedbackValue γ σ 1))
    (hoptN : N.reward γ ψ = ENNReal.ofReal (feedbackValue γ σ 1)) : M = N := by
  obtain ⟨φ', hcφ, hφ₀, hmφ, _, heφ⟩ := M.exists_global_state
  obtain ⟨ψ', hcψ, hψ₀, hmψ, _, heψ⟩ := N.exists_global_state
  have hφeq := M.global_state_unique hM.1 hcφ hM.2.2 heφ
  have hψeq := N.global_state_unique hN.1 hcψ hN.2.2 heψ
  have hφopt : M.reward γ φ' = ENNReal.ofReal (feedbackValue γ σ 1) :=
    (M.reward_eq_of_eqOn γ hφeq).symm.trans hoptM
  have hψopt : N.reward γ ψ' = ENNReal.ofReal (feedbackValue γ σ 1) :=
    (N.reward_eq_of_eqOn γ hψeq).symm.trans hoptN
  exact optimal_mass_unique M N hcφ hcψ hmφ hmψ hφ₀ hψ₀ heφ heψ hγ hσ hgraph hφopt hψopt

/-- For every parameter in the source range, a genuine mass attains the
universal continuum bound, and every attaining admissible string has exactly
that mass. Arbitrary singular mass was allowed in both comparisons. -/
theorem exists_unique_actual_continuum_maximum {γ : ℝ} (hγ : 0 < γ) (hγ₁ : γ ≤ 1) :
    ∃ σ : ℝ → ℝ,
      (∀ r ≥ 1, AnalyticAt ℝ σ r ∧ FeedbackGraphAt γ σ r) ∧
      ∃ M : Mass, ∃ φ : ℝ → ℝ, IsState M φ ∧
        M.reward γ φ = ENNReal.ofReal (Real.sqrt (σ 1) / (2 * γ)) ∧
        (∀ N : Mass, ∀ ψ : ℝ → ℝ, IsState N ψ → N.reward γ ψ ≤ M.reward γ φ) ∧
        ∀ N : Mass, ∀ ψ : ℝ → ℝ, IsState N ψ → N.reward γ ψ = M.reward γ φ → N = M := by
  obtain ⟨σ, hσ, M, φ, hM, hvalue, hbound⟩ := exists_actual_continuum_maximum hγ hγ₁
  refine ⟨σ, hσ, M, φ, hM, hvalue, hbound, ?_⟩
  intro N ψ hN heq
  have hoptM : M.reward γ φ = ENNReal.ofReal (feedbackValue γ σ 1) := by
    rw [hvalue, feedbackValue_one γ σ (hσ 1 le_rfl).2.positive]
  exact hN.mass_unique_of_optimal_reward hM hγ
    (fun r hr ↦ (hσ r hr).1.contDiffAt) (fun r hr ↦ (hσ r hr).2)
    (heq.trans hoptM) hoptM

end
end krylov.Strings
