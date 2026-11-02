import bezout.Probability.Energy
import Mathlib.Algebra.BigOperators.Fin

/-!
Article: bezout, Appendix B, finite physical martingale responses.
Use: converts the natural-time filtration convention to the exact `Fin N`
indexing of a causal history. Values outside the horizon are set to zero;
no probabilistic assumption is imposed there.
Proof: the finite martingale identities and reindexing the horizon sum.
-/

namespace bezout.Probability
noncomputable section
open MeasureTheory
open scoped BigOperators

variable {Ω E F : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  {N : ℕ} {𝓕 : Filtration ℕ mΩ} {w : ℕ → Ω → E}

/-- Extend a finite vector of deterministic physical responses by zero.
Use: matches the finite history to the natural-time martingale convention. -/
def responseExtension (L : Fin N → E →L[ℝ] F) (s : ℕ) : E →L[ℝ] F :=
  if hs : s < N then L ⟨s, hs⟩ else 0

namespace MartingaleDifferences
variable (hw : bezout.Probability.MartingaleDifferences N 𝓕 w μ)
  [IsProbabilityMeasure μ]

include hw

/-- Exact terminal MSE with the physical history's finite call indices.
Use: the response operators will be instantiated by `Phi_s(H)`. -/
theorem integral_norm_sq_finite_response (v : F) (L : Fin N → E →L[ℝ] F) :
    (∫ ω, ‖v + ∑ s : Fin N, L s (w s.val ω)‖ ^ 2 ∂μ) =
      ‖v‖ ^ 2 + ∑ s : Fin N, ∫ ω, ‖L s (w s.val ω)‖ ^ 2 ∂μ := by
  have h := hw.integral_norm_sq_response v (responseExtension L)
  simpa only [Finset.sum_range, responseExtension, Fin.isLt, dite_true] using h

/-- Conditional oracle variance bounds the finite physical-response MSE.
Use: the exact operator energy estimate for an actual N-call history. -/
theorem integral_norm_sq_finite_response_le (v : F) (L : Fin N → E →L[ℝ] F) (σ : ℝ)
    (hσ : ∀ s, s < N → μ[fun ω => ‖w s ω‖ ^ 2 | 𝓕 s] ≤ᵐ[μ] fun _ => σ ^ 2) :
    (∫ ω, ‖v + ∑ s : Fin N, L s (w s.val ω)‖ ^ 2 ∂μ) ≤
      ‖v‖ ^ 2 + σ ^ 2 * ∑ s : Fin N, ‖L s‖ ^ 2 := by
  have h := hw.integral_norm_sq_response_le v (responseExtension L) σ hσ
  simpa only [Finset.sum_range, responseExtension, Fin.isLt, dite_true] using h

/-- Deterministic finite responses preserve the exact nominal mean.
Use: identifies the terminal bias of the actual noisy history. -/
theorem integral_finite_response_sum (v : F) (L : Fin N → E →L[ℝ] F) :
    (∫ ω, v + ∑ s : Fin N, L s (w s.val ω) ∂μ) = v := by
  have h := hw.integral_response_sum v (responseExtension L)
  simpa only [Finset.sum_range, responseExtension, Fin.isLt, dite_true] using h

end MartingaleDifferences
end
end bezout.Probability
