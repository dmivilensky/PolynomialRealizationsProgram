import bezout.Analysis.Energy
import bezout.Analysis.Spectral
import bezout.Probability.History

/-!
Article: bezout, Theorem 3.1, deterministic and martingale upper bounds.
Use: uniform physical response bounds imply the two actual oracle risks.
Proof: exact causal execution, spectral calculus, temporal Cauchy--Schwarz,
and the martingale MSE identity. Errors need not be independent.
-/

namespace bezout.Risk
noncomputable section
open Polynomial MeasureTheory
open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {N : ℕ}

/-- Uniform scalar bounds for the actual physical responses of a history. -/
def ResponseBounds (h : bezout.History N) (I : chebyshev1.SpectralInterval)
    (P : Fin N → ℝ) : Prop :=
  (∀ s, 0 ≤ P s) ∧ ∀ s x, x ∈ Set.Icc I.mu I.L → |(h.response s).eval x| ≤ P s

/-- Any actual deterministic run obeys the response-energy bound. -/
theorem additive_upper (h : bezout.History N) (I : chebyshev1.SpectralInterval)
    (hexact : h.ChebyshevExact I) (H : E →ₗ[ℝ] E) (hH : Analysis.Admissible I H)
    (P : Fin N → ℝ) (hP : ResponseBounds h I P)
    (initial : E) (noise : Fin N → E) (r t : ℝ) (ht : 0 ≤ t)
    (hi : ‖initial‖ ≤ r) (hw : ∑ s, ‖noise s‖ ^ 2 ≤ t ^ 2)
    (u : h.Execution H initial noise) :
    ‖u.output‖ ≤ I.epsilon N * r + t * Analysis.energyNorm P := by
  rw [h.physical_response H initial noise u]
  have hb : ‖(aeval H h.terminal) initial‖ ≤ I.epsilon N * r := by
    rw [hexact]
    exact (Analysis.residual_action_bound I H hH N initial).trans
      (mul_le_mul_of_nonneg_left hi (le_of_lt (one_div_pos.mpr (I.den_pos N))))
  have he : ‖∑ s, (aeval H (h.response s)) (noise s)‖ ≤
      t * Analysis.energyNorm P := by
    calc
      _ ≤ ∑ s, P s * ‖noise s‖ := Analysis.norm_sum_le_energy _ _ (fun s =>
        Analysis.polynomial_action_bound I H hH _ _ (hP.1 s) (hP.2 s) _)
      _ ≤ Analysis.energyNorm P * t := Analysis.sum_mul_le_of_energy ht hw
      _ = _ := mul_comm _ _
  exact (norm_add_le _ _).trans (add_le_add hb he)

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [CompleteSpace E]

/-- Conditional variance and deterministic response bounds control the actual MSE.
The initial state and Hessian are deterministic; martingale errors may be dependent. -/
theorem mse_upper (h : bezout.History N) (I : chebyshev1.SpectralInterval)
    (hexact : h.ChebyshevExact I) (H : E →ₗ[ℝ] E) (hH : Analysis.Admissible I H)
    (P : Fin N → ℝ) (hP : ResponseBounds h I P) (initial : E)
    {𝓕 : Filtration ℕ mΩ} {w : ℕ → Ω → E}
    (hw : bezout.Probability.MartingaleDifferences N 𝓕 w μ) [IsProbabilityMeasure μ]
    (r σ : ℝ) (hr : 0 ≤ r) (hi : ‖initial‖ ≤ r)
    (hσ : ∀ s, s < N → μ[fun ω => ‖w s ω‖ ^ 2 | 𝓕 s] ≤ᵐ[μ] fun _ => σ ^ 2) :
    (∫ ω, ‖h.stochasticOutput H initial w ω‖ ^ 2 ∂μ) ≤
      I.epsilon N ^ 2 * r ^ 2 + σ ^ 2 * ∑ s, P s ^ 2 := by
  have hb : ‖(aeval H h.terminal) initial‖ ≤ I.epsilon N * r := by
    rw [hexact]
    exact (Analysis.residual_action_bound I H hH N initial).trans
      (mul_le_mul_of_nonneg_left hi (le_of_lt (one_div_pos.mpr (I.den_pos N))))
  have hbs : ‖(aeval H h.terminal) initial‖ ^ 2 ≤ I.epsilon N ^ 2 * r ^ 2 := by
    rw [← mul_pow]
    exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg
      (le_of_lt (one_div_pos.mpr (I.den_pos N))) hr)).mpr hb
  have hp : (∑ s, ‖h.responseOperator H s‖ ^ 2) ≤ ∑ s, P s ^ 2 := by
    apply Finset.sum_le_sum
    intro s _
    exact (sq_le_sq₀ (norm_nonneg _) (hP.1 s)).mpr
      (Analysis.polynomial_operator_bound I H hH _ _ (hP.1 s) (hP.2 s))
  exact (h.integral_stochasticOutput_norm_sq_le H initial hw σ hσ).trans
    (add_le_add hbs (mul_le_mul_of_nonneg_left hp (sq_nonneg σ)))

end
end bezout.Risk
