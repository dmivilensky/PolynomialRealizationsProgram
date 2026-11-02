import bezout.Comparisons.Competitors.DFB
import bezout.Probability.FiniteResponse

/-!
Article: bezout, DFB variance coefficient following `eq:competitor-dfb`.
Use: the computed coefficient is the exact variance of the actual averaged
oracle execution, rather than a variance assigned to an internal recurrence.
Proof: actual-error superposition and the martingale finite-response identity;
unit conditional/unconditional variances give the printed closed scalar sum.
-/

namespace bezout.Comparisons.Competitors.DFB
noncomputable section
open MeasureTheory
open scoped BigOperators

/-- The deterministic continuous response of one physical DFB scalar error. -/
def responseOperator (L lam : ℝ) (N : ℕ) (s : Fin N) : ℝ →L[ℝ] ℝ :=
  responseValue L lam N s • ContinuousLinearMap.id ℝ ℝ

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {𝓕 : Filtration ℕ mΩ} {w : ℕ → Ω → ℝ}

/-- Exact MSE of the actual DFB averaged execution under the martingale model. -/
theorem integral_output_sq (L lam initial : ℝ) (N : ℕ)
    (hw : bezout.Probability.MartingaleDifferences N 𝓕 w μ) :
    (∫ ω, (output L N (Momentum.scalarOracle N lam (fun s => w s.val ω)) initial)^2 ∂μ) =
      (terminalValue L lam N*initial)^2+
        ∑ s : Fin N, responseValue L lam N s^2*(∫ ω, (w s.val ω)^2 ∂μ) := by
  have he (ω : Ω) : output L N (Momentum.scalarOracle N lam (fun s => w s.val ω)) initial =
      terminalValue L lam N*initial+∑ s : Fin N, responseOperator L lam N s (w s.val ω) := by
    simpa only [responseOperator,smul_apply,
      ContinuousLinearMap.id_apply,smul_eq_mul] using
      output_superposition L lam N initial (fun s => w s.val ω)
  simp_rw [he]
  have hm := hw.integral_norm_sq_finite_response (terminalValue L lam N*initial) (responseOperator L lam N)
  simp only [Real.norm_eq_abs,sq_abs] at hm
  rw [hm]
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  simp only [responseOperator,smul_apply,
    ContinuousLinearMap.id_apply,smul_eq_mul,mul_pow]
  exact integral_const_mul _ _

/-- Equal physical error variances give exactly sigma squared times the finite coefficient. -/
theorem integral_output_sq_equal_variances (L lam initial σ : ℝ) (N : ℕ)
    (hw : bezout.Probability.MartingaleDifferences N 𝓕 w μ)
    (hσ : ∀ s, s<N → (∫ ω, (w s ω)^2 ∂μ)=σ^2) :
    (∫ ω, (output L N (Momentum.scalarOracle N lam (fun s => w s.val ω)) initial)^2 ∂μ) =
      (terminalValue L lam N*initial)^2+σ^2*varianceValue L lam N := by
  rw [integral_output_sq L lam initial N hw]
  simp only [hσ _ (Fin.is_lt _),varianceValue,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  ring

end
end bezout.Comparisons.Competitors.DFB
