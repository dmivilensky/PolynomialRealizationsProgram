import krylov.OneGradient.ScenarioOperators
import krylov.Secant.Trajectory
set_option autoImplicit false
/-!
Article: main_krylov, thm:local, exact native/source canonical increments.
Use: native varying-operator formulas retain precisely the original
individual query and independent output budgets in any genuine metric.
Source: exact source operator extension and actual physical increment
dictionaries, including every empty and post-output slot.
-/

namespace krylov.OneGradient
noncomputable section
open Matrix krylov.Reference krylov.Methods krylov.Secant krylov.Information
variable {p : ℕ}

/-- The genuine first native source operator is exactly its actual base.
Use: the true known-base prior term refers to the original physical base.
Article: main_krylov, thm:local, original base dictionary.
Proof: the first real probe has an empty increment prefix. -/
theorem oneGradientScenarioMatrices_zero (S : Scenario p) (N : ℕ) :
    oneGradientScenarioMatrices S N 0=S.base := by
  rw [oneGradientScenarioMatrices_probe S N 0 (Nat.zero_le N)]
  simp only [Scenario.probe,Finset.sum_range_zero,add_zero]

/-- Every actual canonical increment of the native source extension is
exactly its original query increment, output defect or zero post-output
slot in the same real reference metric.
Use: actual source budgets enter native output formulas without any
index shift, unobserved-query assumption or hidden terminal increment.
Article: main_krylov, thm:local, complete canonical increment dictionary.
Proof: use the genuine physical query/output increment identities. After
the output slot the true extension is constant, so its increment is zero. -/
theorem oneGradientScenarioMatrices_canonicalIncrement
    (base : Matrix (Fin p) (Fin p) ℝ) (S : Scenario p) (N l : ℕ) :
    canonicalIncrement base (oneGradientScenarioMatrices S N) l=
      if l<N then relativeOperator base (S.increment l)
      else if l=N then relativeOperator base S.terminal else 0 := by
  by_cases hl : l<N
  · rw [ite_eq_left hl,canonicalIncrement,oneGradientScenarioMatrices_increment S N l hl]
  · rw [ite_eq_right hl]
    by_cases he : l=N
    · subst l
      rw [ite_eq_left rfl,canonicalIncrement,oneGradientScenarioMatrices_terminal]
    · rw [ite_eq_right he]
      have h1 : ¬l+1≤N := by omega
      have h2 : ¬l≤N := by omega
      simp only [canonicalIncrement,oneGradientScenarioMatrices,ite_eq_right h1,ite_eq_right h2,
        sub_self,relativeOperator,Matrix.mul_zero,Matrix.zero_mul]

end
end krylov.OneGradient
