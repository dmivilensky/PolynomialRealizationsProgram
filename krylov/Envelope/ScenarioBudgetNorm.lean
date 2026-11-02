import krylov.Envelope.ScenarioBudgets

set_option autoImplicit false
/-!
Article: main_krylov, thm:E and s3:cor:qn, actual finite scenario radius.
Use: bound the genuine finite source scenario norm by the true largest
nonnegative increment budget, including empty and zero profiles.
Source: genuine independent spectral budgets and the standard finite
product supremum norm identities.
-/

namespace krylov.Envelope
noncomputable section
open scoped Matrix.Norms.L2Operator NNReal
variable {n N : ℕ}

/-- Every actual increment array in its genuine source budget has finite product norm at most the true largest budget.
Use: Every actual increment array in its genuine source budget has finite product norm at most the true largest budget.
Article: main_krylov, thm:E and s3:cor:qn, actual finite scenario radius.
Proof: Each actual spectral norm is bounded by its assigned budget, which is at most the genuine finite budget supremum. -/
theorem incrementBudget_norm_le (ω : Fin (N-1) → ℝ≥0)
    (E : Fin (N-1) → Matrix (Fin n) (Fin n) ℝ) (hE : E∈incrementBudget N ω) :
    ‖E‖≤(maximalBudget ω : ℝ) := by
  apply (pi_norm_le_iff_of_nonneg (maximalBudget ω).coe_nonneg).mpr
  intro i
  exact (hE i).2.trans (by exact_mod_cast Finset.le_sup (f := ω) (Finset.mem_univ i))

/-- Every genuine full source scenario has actual finite product norm at most its true largest increment budget.
Use: Every genuine full source scenario has actual finite product norm at most its true largest increment budget.
Article: main_krylov, thm:E and s3:cor:qn, actual finite scenario radius.
Proof: Use the real increment bound and the actual correction-defect budget in the genuine product supremum norm. -/
theorem scenarioBudget_norm_le (ω : Fin (N-1) → ℝ≥0) (Θ : CanonicalScenario n N)
    (hΘ : Θ∈scenarioBudget N ω) : ‖Θ‖≤(maximalBudget ω : ℝ) := by
  rw [Prod.norm_def]
  exact max_le (incrementBudget_norm_le ω Θ.1 hΘ.1)
    ((pi_norm_le_iff_of_nonneg (maximalBudget ω).coe_nonneg).mpr (fun k => (hΘ.2 k).2))
end
end krylov.Envelope
