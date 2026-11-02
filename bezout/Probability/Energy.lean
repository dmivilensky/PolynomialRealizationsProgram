import bezout.Probability.Martingale

/-!
Article: bezout, Equation (8) and Appendix B (the conditional variance budget).
Use: converts the oracle's conditional second-moment bound into the exact
physical-response MSE estimate needed for the Flat construction.
Proof: integrate the conditional expectation, apply the deterministic operator
norm bound to each response, and use the proved martingale Pythagorean identity.
-/

namespace bezout.Probability.MartingaleDifferences

open MeasureTheory Filter
open scoped BigOperators
noncomputable section

variable {Ω E F : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  {N : ℕ} {𝓕 : Filtration ℕ mΩ} {w : ℕ → Ω → E}
  (hw : bezout.Probability.MartingaleDifferences N 𝓕 w μ) [IsProbabilityMeasure μ]

include hw

omit [InnerProductSpace ℝ E] [CompleteSpace E] hw in
/-- The conditional energy budget bounds the unconditional second moment.
Article: bezout, Equation (8). Use: the bound is valid for dependent martingale
errors, without imposing independence or a deterministic magnitude bound. -/
theorem integral_energy_le (σ : ℝ)
    (hσ : ∀ s, s < N → μ[fun ω => ‖w s ω‖ ^ 2 | 𝓕 s] ≤ᵐ[μ] fun _ => σ ^ 2)
    (s : ℕ) (hs : s < N) : (∫ ω, ‖w s ω‖ ^ 2 ∂μ) ≤ σ ^ 2 := by
  have h := integral_mono_ae integrable_condExp (integrable_const (μ := μ) (σ ^ 2)) (hσ s hs)
  rw [integral_condExp (𝓕.le s)] at h
  simpa using h

omit [CompleteSpace E] [CompleteSpace F] in
/-- A deterministic physical response incurs its operator norm squared times
the oracle energy. Article: bezout, Appendix B. Use: uniform finite MSE upper bounds. -/
theorem integral_response_energy_le (L : E →L[ℝ] F) (σ : ℝ)
    (hσ : ∀ s, s < N → μ[fun ω => ‖w s ω‖ ^ 2 | 𝓕 s] ≤ᵐ[μ] fun _ => σ ^ 2)
    (s : ℕ) (hs : s < N) :
    (∫ ω, ‖L (w s ω)‖ ^ 2 ∂μ) ≤ ‖L‖ ^ 2 * σ ^ 2 := by
  have hint := (hw.squareIntegrable s hs).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  calc
    _ ≤ ∫ ω, ‖L‖ ^ 2 * ‖w s ω‖ ^ 2 ∂μ := by
      apply integral_mono_ae
        (((hw.squareIntegrable s hs).continuousLinearMap_comp L).integrable_norm_pow
          (by norm_num : (2 : ℕ) ≠ 0)) (hint.const_mul _)
      exact Eventually.of_forall fun ω => by
        have h := (sq_le_sq₀ (norm_nonneg (L (w s ω)))
          (mul_nonneg (norm_nonneg L) (norm_nonneg (w s ω)))).mpr (L.le_opNorm (w s ω))
        simpa only [mul_pow] using h
    _ = ‖L‖ ^ 2 * ∫ ω, ‖w s ω‖ ^ 2 ∂μ := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left (integral_energy_le σ hσ s hs) (sq_nonneg _)

/-- The exact terminal MSE is bounded by the sum of squared physical operator
responses. Article: bezout, Theorem 3.1, upper-bound ingredient in Appendix B.
Use: the Flat factorization will make every operator response at most S_N/N. -/
theorem integral_norm_sq_response_le (v : F) (L : ℕ → E →L[ℝ] F) (σ : ℝ)
    (hσ : ∀ s, s < N → μ[fun ω => ‖w s ω‖ ^ 2 | 𝓕 s] ≤ᵐ[μ] fun _ => σ ^ 2) :
    (∫ ω, ‖v + ∑ s ∈ Finset.range N, L s (w s ω)‖ ^ 2 ∂μ) ≤
      ‖v‖ ^ 2 + σ ^ 2 * ∑ s ∈ Finset.range N, ‖L s‖ ^ 2 := by
  rw [hw.integral_norm_sq_response v L]
  apply add_le_add_right
  calc
    _ ≤ ∑ s ∈ Finset.range N, ‖L s‖ ^ 2 * σ ^ 2 :=
      Finset.sum_le_sum fun s hs => hw.integral_response_energy_le (L s) σ hσ s
        (Finset.mem_range.mp hs)
    _ = _ := by rw [← Finset.sum_mul]; ring

/-- Martingale oracle errors introduce no terminal mean bias through fixed
linear responses. Article: bezout, Appendix B. Use: distinguishes exact bias
from variance before applying the sharp MSE bound. -/
theorem integral_response_sum (v : F) (L : ℕ → E →L[ℝ] F) :
    (∫ ω, v + ∑ s ∈ Finset.range N, L s (w s ω) ∂μ) = v := by
  have hint (s : ℕ) (hs : s ∈ Finset.range N) : Integrable (fun ω => L s (w s ω)) μ :=
    (L s).integrable_comp ((hw.squareIntegrable s (Finset.mem_range.mp hs)).integrable
      (by norm_num))
  rw [integral_add (integrable_const v) (integrable_finsetSum _ hint),
    integral_finsetSum _ hint]
  have hz : (∑ s ∈ Finset.range N, ∫ ω, L s (w s ω) ∂μ) = 0 := by
    apply Finset.sum_eq_zero
    intro s hs
    rw [(L s).integral_comp_comm
      ((hw.squareIntegrable s (Finset.mem_range.mp hs)).integrable (by norm_num)),
      hw.integral_eq_zero s (Finset.mem_range.mp hs), map_zero]
  simp [hz]

end
end bezout.Probability.MartingaleDifferences
