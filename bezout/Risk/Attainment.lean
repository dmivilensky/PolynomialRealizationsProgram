import bezout.Risk.Minimax

/-!
Article: bezout, Theorem 3.1, equality cases for the two additive risks.
Use: the Flat construction supplies the single equal-response hypothesis
below; all dimensions, physical executions and martingale models are then
quantified by the risk definitions, not by additional certificates.
Proof: universal upper bounds and the actual scalar attaining examples.
-/

namespace bezout.Risk
noncomputable section
open scoped BigOperators
variable {N : ℕ}

/-- Equal response bounds have exactly the temporal norm `S_N/sqrt N`. -/
theorem equal_response_energy (I : chebyshev1.SpectralInterval) (hN : 0 < N) :
    Analysis.energyNorm (fun _ : Fin N => Lower.additiveScale I N / N) =
      Lower.additiveScale I N / Real.sqrt N := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hs : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hn
  apply (sq_eq_sq₀ (Analysis.energyNorm_nonneg _) (div_nonneg
    (additiveScale_nonneg I N) hs.le)).mp
  simp only [Analysis.energyNorm_sq, div_pow, Real.sq_sqrt hn.le,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

/-- The corresponding squared response sum is exactly `S_N^2/N`. -/
theorem equal_response_sq_sum (I : chebyshev1.SpectralInterval) (hN : 0 < N) :
    (∑ _ : Fin N, (Lower.additiveScale I N / N) ^ 2) =
      Lower.additiveScale I N ^ 2 / N := by
  have hn : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

/-- Equal uniform physical responses attain the exact universal deterministic risk. -/
theorem additiveRisk_eq_of_equal_responses (h : bezout.History N)
    (I : chebyshev1.SpectralInterval) (he : h.ChebyshevExact I) (hN : 0 < N)
    (hP : ∀ s x, x ∈ Set.Icc I.mu I.L →
      |(h.response s).eval x| ≤ Lower.additiveScale I N / N)
    (r t : ℝ) (hr : 0 ≤ r) (ht : 0 ≤ t) :
    additiveRisk h I r t = additiveOptimum I N r t := by
  have hb : AdditiveBound h I r t (additiveOptimum I N r t) := by
    intro E _ _ _ H hH initial w hi hw u
    have hu := additive_upper h I he H hH
      (fun _ => Lower.additiveScale I N / N)
      ⟨fun _ => div_nonneg (additiveScale_nonneg I N) (Nat.cast_nonneg N), hP⟩
      initial w r t ht hi hw u
    simpa only [equal_response_energy I hN, additiveOptimum, mul_div_assoc] using hu
  apply le_antisymm
  · exact csInf_le ⟨additiveOptimum I N r t,
      fun C hc => additiveBound_lower h I he hN r t C hr ht hc⟩ hb
  · exact additiveRisk_lower h I he hN r t hr ht

/-- The same equal-response history attains the exact worst-case martingale MSE. -/
theorem mseRisk_eq_of_equal_responses (h : bezout.History N)
    (I : chebyshev1.SpectralInterval) (he : h.ChebyshevExact I) (hN : 0 < N)
    (hP : ∀ s x, x ∈ Set.Icc I.mu I.L →
      |(h.response s).eval x| ≤ Lower.additiveScale I N / N)
    (r σ : ℝ) (hr : 0 ≤ r) : mseRisk h I r σ = mseOptimum I N r σ := by
  have hb : MseBound h I r σ (mseOptimum I N r σ) := by
    intro E Ω _ _ _ _ _ μ _ 𝓕 w hw hσ H hH initial hi
    have hu := mse_upper h I he H hH (fun _ => Lower.additiveScale I N / N)
      ⟨fun _ => div_nonneg (additiveScale_nonneg I N) (Nat.cast_nonneg N), hP⟩
      initial hw r σ hr hi hσ
    simpa only [equal_response_sq_sum I hN, mseOptimum, mul_div_assoc] using hu
  apply le_antisymm
  · exact csInf_le ⟨mseOptimum I N r σ,
      fun C hc => mseBound_lower h I he hN r σ C hr hc⟩ hb
  · exact mseRisk_lower h I he hN r σ hr

end
end bezout.Risk
