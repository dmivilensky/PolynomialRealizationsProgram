import krylov.Strings.OptimizerFiniteNoAttainment

/-!
Article: main_krylov, thm:value, maximum over all admitted physical lengths.
Use: combine the unique actual half-line maximum with strict nonattainment
for every finite endpoint, including sources with unbounded terminal mass.
Source: the actual global maximum and the finite equality-to-feedback argument.
-/

/-!
Article: krylov, Theorem D.8 [thm:value].

The actual all-length optimizer exists uniquely, has the stated analytic positive density, and
the same mass has its canonical principal probability measure, zero atom and exact high-
frequency tail.
ActualRegularMaximum is not an input optimizer certificate: the exists theorems construct it.
Finite-length strings, singular mass and endpoint blowup are included among competitors.
-/

namespace krylov.Strings
noncomputable section
open Set Filter MeasureTheory
open krylov.ContinuumControl
open scoped Topology NNReal ENNReal

/-- The source continuum variational theorem over all physical lengths:
an actual unique half-line string attains the sharp value, every other
admissible half-line mass is bounded by it, and every finite-length string
has strictly smaller reward. Only original state equations are admissibility
hypotheses; smoothness, positivity and absence of singular mass are conclusions.
-/
theorem exists_unique_actual_all_lengths_maximum {γ : ℝ} (hγ : 0 < γ) (hγ₁ : γ ≤ 1) :
    ∃ σ : ℝ → ℝ,
      (∀ r ≥ 1, AnalyticAt ℝ σ r ∧ FeedbackGraphAt γ σ r) ∧
      ∃ M : Mass, ∃ φ : ℝ → ℝ, IsState M φ ∧
        M.reward γ φ = ENNReal.ofReal (Real.sqrt (σ 1) / (2 * γ)) ∧
        (∀ N : Mass, ∀ ψ : ℝ → ℝ, IsState N ψ → N.reward γ ψ ≤ M.reward γ φ) ∧
        (∀ N : Mass, ∀ ψ : ℝ → ℝ, IsState N ψ → N.reward γ ψ = M.reward γ φ → N = M) ∧
        ∀ (ℓ : ℝ) (hℓ : 0 < ℓ) (f : StieltjesFunction (Ico (0 : ℝ) ℓ))
          (h₀ : f ⟨0, ⟨le_rfl, hℓ⟩⟩ = 1) (ψ : ℝ → ℝ),
          ContinuousOn ψ (Iio ℓ) →
          (∀ w : OptimizerFinite.Windows ℓ, ∀ x ∈ Icc 0 (w.val : ℝ), ψ x = 1 +
            ∫ t in Ioc 0 x, integralSlope (OptimizerFinite.windowMass hℓ f h₀ w).measure ψ t) →
          OptimizerFinite.reward hℓ f h₀ γ ψ < M.reward γ φ := by
  obtain ⟨σ, hσ, M, φ, hM, hvalue, hbound, hunique⟩ := exists_unique_actual_continuum_maximum hγ hγ₁
  refine ⟨σ, hσ, M, φ, hM, hvalue, hbound, hunique, ?_⟩
  intro ℓ hℓ f h₀ ψ hc he
  have hopt : M.reward γ φ = ENNReal.ofReal (feedbackValue γ σ 1) := by
    rw [hvalue, feedbackValue_one γ σ (hσ 1 le_rfl).2.positive]
  rw [hopt]
  exact OptimizerFinite.reward_lt_of_state M hM hγ
    (fun r hr ↦ (hσ r hr).1.contDiffAt) (fun r hr ↦ (hσ r hr).2)
    hopt hℓ f h₀ hc he

end
end krylov.Strings
