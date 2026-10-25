import polyak.Growth.Plateau
import polyak.Growth.OriginalRate

/-!
Article: Theorem spectralgeneral(b).
Use: pass from dimension-uniform finite-window energy estimates to a strict upper rate.
Proof: the energy estimate is impossible at the exact growth exponent.
-/

namespace polyak.Growth
noncomputable section

/-- Article: strict upper growth bound. Use: an estimate at every exponent above a threshold
forces the exact free-state growth rate strictly below that threshold. -/
theorem growthRate_lt_exp_of_windows {A B β t₀ : ℝ} (hB : B ≠ 0)
    (henergy : ∀ t : ℝ, t₀ ≤ t →
      ∃ (K : ℝ) (w : ℕ), 0 < K ∧ WindowEnergyBound A B β t K w) :
    growthRate A B β < Real.exp t₀ := by
  by_contra h
  have ht : t₀ ≤ Real.log (growthRate A B β) := by
    rw [← Real.exp_le_exp, Real.exp_log (growthRate_pos A B β)]
    exact le_of_not_gt h
  obtain ⟨K,w,hK,hwindow⟩ := henergy (Real.log (growthRate A B β)) ht
  exact not_windowEnergyBound_at_growth hB hK hwindow

/-- Article: original strict upper rate. Use: the source initialization and the supremum
over all dimensions inherit the strict free-state upper estimate. -/
theorem originalRate_lt_exp_of_windows {μ L α β t₀ : ℝ}
    (hμ : 0 < μ) (hL : μ < L) (hα : 0 < α) (hβ : 0 ≤ β)
    (henergy : ∀ t : ℝ, t₀ ≤ t → ∃ (K : ℝ) (w : ℕ), 0 < K ∧
      WindowEnergyBound (Dynamics.normalizedA μ L α β) (Dynamics.normalizedB μ L α) β t K w) :
    Dynamics.rate μ L α β < Real.exp t₀ := by
  have hB : Dynamics.normalizedB μ L α ≠ 0 := by
    dsimp [Dynamics.normalizedB]
    positivity
  exact (originalRate_le_growthRate hμ hL hα hβ).trans_lt
    (growthRate_lt_exp_of_windows hB henergy)

end
end polyak.Growth
