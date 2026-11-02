import bezout.Properties.Incompatibility

/-!
Article: bezout, Appendix B classical comparison and Appendix D predictions.
Use: simultaneous endpoint attainment of unequal response bounds gives the
literal worst-case risks of a fixed Chebyshev-exact history.
Proof: the universal physical response bounds and actual scalar endpoint
executions give matching inequalities. No equal-response assumption is needed.
-/

namespace bezout.Risk
noncomputable section
open scoped BigOperators
variable {N : ℕ}

/-- Endpoint attainment identifies the temporal response energy exactly. -/
theorem endpoint_response_energy (h : bezout.History N) (I : chebyshev1.SpectralInterval)
    (P : Fin N → ℝ) (hp : ∀ s, |(h.response s).eval I.mu| = P s) :
    (∑ s, (h.response s).eval I.mu ^ 2) = ∑ s, P s ^ 2 := by
  apply Finset.sum_congr rfl
  intro s _
  rw [← sq_abs, hp]

/-- A fixed exact history with jointly sharp endpoint response bounds has this
exact worst-case martingale MSE, even when its temporal bounds are unequal. -/
theorem mseRisk_eq_of_endpoint_bounds (h : bezout.History N)
    (I : chebyshev1.SpectralInterval) (he : h.ChebyshevExact I) (hN : 0 < N)
    (P : Fin N → ℝ) (hP : ResponseBounds h I P)
    (hp : ∀ s, |(h.response s).eval I.mu| = P s) (r σ : ℝ) (hr : 0 ≤ r) :
    mseRisk h I r σ = I.epsilon N ^ 2 * r ^ 2 + σ ^ 2 * ∑ s, P s ^ 2 := by
  apply le_antisymm
  · apply csInf_le ⟨mseOptimum I N r σ, fun C hb => mseBound_lower h I he hN r σ C hr hb⟩
    intro E Ω _ _ _ _ _ μ _ 𝓕 w hw hσ H hH initial hi
    exact mse_upper h I he H hH P hP initial hw r σ hr hi hσ
  · simpa only [endpoint_response_energy h I P hp] using
      bezout.Properties.scalar_mse_le_risk h I he r σ hr

/-- Joint endpoint attainment also gives the exact shared-energy terminal distance. -/
theorem additiveRisk_eq_of_endpoint_bounds (h : bezout.History N)
    (I : chebyshev1.SpectralInterval) (he : h.ChebyshevExact I) (hN : 0 < N)
    (P : Fin N → ℝ) (hP : ResponseBounds h I P)
    (hp : ∀ s, |(h.response s).eval I.mu| = P s)
    (r t : ℝ) (hr : 0 ≤ r) (ht : 0 ≤ t) :
    additiveRisk h I r t = I.epsilon N * r + t * Analysis.energyNorm P := by
  apply le_antisymm
  · apply csInf_le ⟨additiveOptimum I N r t,
      fun C hb => additiveBound_lower h I he hN r t C hr ht hb⟩
    intro E _ _ _ H hH initial w hi hw u
    exact additive_upper h I he H hH P hP initial w r t ht hi hw u
  · obtain ⟨w, hw, hout⟩ := scalar_additive_attainment h I he r t hr ht
    have heq : Analysis.energyNorm (fun s => (h.response s).eval I.mu) = Analysis.energyNorm P := by
      unfold Analysis.energyNorm
      rw [endpoint_response_energy h I P hp]
    rw [heq] at hout
    apply le_csInf (additiveBounds_nonempty h I he r t ht)
    intro C hb
    have hu := hb ℝ (bezout.History.scalarOperator I.mu)
      (Analysis.scalar_admissible I I.mu ⟨le_rfl, I.mu_lt_L.le⟩) r w
      (by simp [abs_of_nonneg hr]) hw (h.run _ r w)
    simpa only [hout] using hu

end
end bezout.Risk
