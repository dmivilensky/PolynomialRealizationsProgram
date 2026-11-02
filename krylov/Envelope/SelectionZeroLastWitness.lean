import krylov.Envelope.SelectionInformationBound
import krylov.Envelope.SelectionBoundary
import krylov.Envelope.ScenarioBudgetUpdates

set_option autoImplicit false
/-!
Article: main_krylov, s3:thm:cf, zero-last-increment selection witness.
Use: reserve the entire last increment budget while attaining the actual selection lower bound.
Source: the proved genuine selection witness, last-budget invariance and monotonicity of the full scenario budget.
-/

namespace krylov.Envelope
noncomputable section
open krylov.Reference krylov.Methods Matrix
open scoped Matrix.Norms.L2Operator NNReal
variable {n : ℕ}

/-- Every actual smooth method has a selection witness whose last increment vanishes.
Use: Every actual smooth method has a selection witness whose last increment vanishes.
Article: main_krylov, s3:thm:cf, zero-last-increment selection witness.
Proof: Set only the final budget to zero, use actual selection attainment, and include the smaller genuine scenario budget. -/
theorem selection_zero_last_witness (M : SmoothProbedClass (EuclideanSpace ℝ (Fin n)))
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (g : EuclideanSpace ℝ (Fin n))
    (N : ℕ) (hN : 2≤N) (hcount : N≤referenceAtomCount base hb g) (ω : Fin (N-1) → ℝ≥0) :
    ∃ Θ∈scenarioBudget N ω, Θ.1 ⟨N-2,by omega⟩=0 ∧
      ‖scenarioVariation M.policy base g N Θ‖=selectionValue base g N ω := by
  classical
  -- The tilt ignores the last budget, so setting that budget to zero preserves the exact value.
  let l : Fin (N-1) := ⟨N-2,by omega⟩
  let η := Function.update ω l 0
  have hη : η≤ω := by
    intro j
    by_cases hj : j=l
    · subst j
      simp only [η,Function.update_self]
      exact bot_le
    · simp only [η,Function.update_of_ne hj]
      exact le_rfl
  have hval : selectionValue base g N η=selectionValue base g N ω := by
    apply selectionValue_congr_early base hb g N hN hcount η ω
    intro j hj
    have hne : j≠l := by
      intro he
      have hv := congrArg Fin.val he
      dsimp only [l] at hv
      omega
    exact Function.update_of_ne hne _ _
  -- The actual lower witness for the smaller budget has a genuinely zero final increment.
  obtain ⟨Θ,hΘ,hv⟩ := selection_lower_witness M base hb g N hN hcount η
  have hz : Θ.1 l=0 := by
    have hn : ‖Θ.1 l‖≤0 := by
      simpa only [η,Function.update_self,NNReal.coe_zero] using (hΘ.1 l).2
    exact norm_eq_zero.mp (le_antisymm hn (norm_nonneg _))
  exact ⟨Θ,scenarioBudget_mono η ω hη hΘ,hz,hv.trans hval⟩
end
end krylov.Envelope
