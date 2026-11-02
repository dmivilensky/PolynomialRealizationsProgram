import bezout.Probability.FiniteResponse
import bezout.History.Execution
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
Article: bezout, Equation (8), Theorem 3.1 and Appendix B.
Use: connects the actual causal oracle execution to the exact martingale MSE
identity, conditional variance upper bound and adapted-query requirement.
Proof: deterministic polynomial response operators act continuously in finite
dimension; exact execution semantics then reduce to the finite response
identities. Adaptation follows directly from the strictly causal recursion.
-/

namespace bezout.History
noncomputable section
open Polynomial MeasureTheory
open scoped BigOperators

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] {N : ℕ}

/-- The deterministic physical response of an actual oracle call, as a continuous operator.
Use: the martingale calculation is applied to `Phi_s(H)` from the actual history. -/
def responseOperator (h : bezout.History N) (H : E →ₗ[ℝ] E) (s : Fin N) : E →L[ℝ] E :=
  (aeval H (h.response s)).toContinuousLinearMap

omit [CompleteSpace E] in
/-- The continuous physical response is exactly polynomial evaluation in the Hessian.
Use: transports the deterministic execution identity into probability theory. -/
@[simp] theorem responseOperator_apply (h : bezout.History N) (H : E →ₗ[ℝ] E)
    (s : Fin N) (v : E) : h.responseOperator H s v = (aeval H (h.response s)) v := rfl

/-- The actual random output produced by the causal noisy oracle history.
Use: this is the terminal error whose expectation and MSE are bounded. -/
def stochasticOutput (h : bezout.History N) (H : E →ₗ[ℝ] E)
    (initial : E) (w : ℕ → Ω → E) (ω : Ω) : E :=
  (h.run H initial (fun s => w s.val ω)).output

omit [CompleteSpace E] in
/-- Every sample of the actual terminal has the exact physical-response decomposition.
Use: introduces no probabilistic surrogate or additional oracle execution. -/
theorem stochasticOutput_response (h : bezout.History N) (H : E →ₗ[ℝ] E)
    (initial : E) (w : ℕ → Ω → E) (ω : Ω) :
    h.stochasticOutput H initial w ω = (aeval H h.terminal) initial +
      ∑ s : Fin N, h.responseOperator H s (w s.val ω) := by
  exact h.physical_response H initial (fun s => w s.val ω)
    (h.run H initial (fun s => w s.val ω))

/-- Exact MSE of the actual history under the article's martingale oracle assumptions.
Use: the stochastic part of Theorem 3.1, before inserting the Flat response bound. -/
theorem integral_stochasticOutput_norm_sq (h : bezout.History N) (H : E →ₗ[ℝ] E)
    (initial : E) {𝓕 : Filtration ℕ mΩ} {w : ℕ → Ω → E}
    (hw : bezout.Probability.MartingaleDifferences N 𝓕 w μ) [IsProbabilityMeasure μ] :
    (∫ ω, ‖h.stochasticOutput H initial w ω‖ ^ 2 ∂μ) =
      ‖(aeval H h.terminal) initial‖ ^ 2 +
        ∑ s : Fin N, ∫ ω, ‖h.responseOperator H s (w s.val ω)‖ ^ 2 ∂μ := by
  simp_rw [h.stochasticOutput_response H initial w]
  exact hw.integral_norm_sq_finite_response _ _

/-- The article's conditional variance budget bounds the actual terminal MSE.
Use: applicable to temporally dependent errors with deterministic history coefficients. -/
theorem integral_stochasticOutput_norm_sq_le (h : bezout.History N) (H : E →ₗ[ℝ] E)
    (initial : E) {𝓕 : Filtration ℕ mΩ} {w : ℕ → Ω → E}
    (hw : bezout.Probability.MartingaleDifferences N 𝓕 w μ) [IsProbabilityMeasure μ]
    (σ : ℝ) (hσ : ∀ s, s < N →
      μ[fun ω => ‖w s ω‖ ^ 2 | 𝓕 s] ≤ᵐ[μ] fun _ => σ ^ 2) :
    (∫ ω, ‖h.stochasticOutput H initial w ω‖ ^ 2 ∂μ) ≤
      ‖(aeval H h.terminal) initial‖ ^ 2 +
        σ ^ 2 * ∑ s : Fin N, ‖h.responseOperator H s‖ ^ 2 := by
  simp_rw [h.stochasticOutput_response H initial w]
  exact hw.integral_norm_sq_finite_response_le _ _ σ hσ

/-- The mean of the actual noisy terminal equals the noiseless terminal exactly.
Use: the decomposition of terminal bias and stochastic variance in Appendix B. -/
theorem integral_stochasticOutput (h : bezout.History N) (H : E →ₗ[ℝ] E)
    (initial : E) {𝓕 : Filtration ℕ mΩ} {w : ℕ → Ω → E}
    (hw : bezout.Probability.MartingaleDifferences N 𝓕 w μ) [IsProbabilityMeasure μ] :
    (∫ ω, h.stochasticOutput H initial w ω ∂μ) = (aeval H h.terminal) initial := by
  simp_rw [h.stochasticOutput_response H initial w]
  exact hw.integral_finite_response_sum _ _

omit [CompleteSpace E] in
/-- Each actual oracle answer is measurable immediately after its own call.
Use: strict causality realizes the filtration convention in Equation (8). -/
theorem stochastic_answers_adapted (h : bezout.History N) (H : E →ₗ[ℝ] E)
    (initial : E) {𝓕 : Filtration ℕ mΩ} {w : ℕ → Ω → E}
    (hw : bezout.Probability.MartingaleDifferences N 𝓕 w μ) (s : Fin N) :
    StronglyMeasurable[𝓕 (s.val + 1)]
      (fun ω => h.answers H initial (fun j => w j.val ω) s) := by
  induction s using (measure (fun s : Fin N => s.val)).wf.induction with
  | h s ih =>
    have heq : (fun ω => h.answers H initial (fun j => w j.val ω) s) =
        (fun ω => H (initial - ∑ j : Fin N,
          h.a s j • h.answers H initial (fun k => w k.val ω) j) + w s.val ω) := by
      funext ω
      exact h.answers_eq H initial (fun j => w j.val ω) s
    rw [heq]
    apply ((H.toContinuousLinearMap).continuous.comp_stronglyMeasurable ?_).add
      (hw.adapted s.val s.isLt)
    apply stronglyMeasurable_const.sub
    apply Finset.stronglyMeasurable_fun_sum Finset.univ
    intro j _
    by_cases hj : j < s
    · exact ((ih j hj).mono (𝓕.mono (by omega))).const_smul (h.a s j)
    · simp only [h.triangular s j (le_of_not_gt hj), zero_smul]
      exact stronglyMeasurable_const

omit [CompleteSpace E] in
/-- Each actual query is measurable before its own oracle call.
Use: verifies the article's predictable-query condition for the realized noisy history. -/
theorem stochastic_query_adapted (h : bezout.History N) (H : E →ₗ[ℝ] E)
    (initial : E) {𝓕 : Filtration ℕ mΩ} {w : ℕ → Ω → E}
    (hw : bezout.Probability.MartingaleDifferences N 𝓕 w μ) (s : Fin N) :
    StronglyMeasurable[𝓕 s.val]
      (fun ω => (h.run H initial (fun j => w j.val ω)).query s) := by
  change StronglyMeasurable[𝓕 s.val] (fun ω => initial - ∑ j : Fin N,
    h.a s j • h.answers H initial (fun k => w k.val ω) j)
  apply stronglyMeasurable_const.sub
  apply Finset.stronglyMeasurable_fun_sum Finset.univ
  intro j _
  by_cases hj : j < s
  · exact ((h.stochastic_answers_adapted H initial hw j).mono (𝓕.mono (by omega))).const_smul
      (h.a s j)
  · simp only [h.triangular s j (le_of_not_gt hj), zero_smul]
    exact stronglyMeasurable_const

end
end bezout.History
