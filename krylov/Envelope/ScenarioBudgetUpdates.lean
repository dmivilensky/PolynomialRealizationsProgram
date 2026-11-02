import krylov.Envelope.ScenarioBudgets

set_option autoImplicit false
/-!
Article: main_krylov, s3:thm:cf, genuine source budget monotonicity and fresh insertion.
Use: enlarge actual finite source budgets and insert a real newest
symmetric increment into a genuine zero slot without losing any true budget.
Source: real finite nonnegative budget suprema and actual independent
symmetric spectral source budget coordinates.
-/

namespace krylov.Envelope
noncomputable section
open Matrix Set
open scoped Matrix.Norms.L2Operator NNReal
variable {n N : ℕ}

/-- The actual largest nonnegative source budget increases with every genuine budget coordinate.
Use: The actual largest nonnegative source budget increases with every genuine budget coordinate.
Article: main_krylov, s3:thm:cf, genuine source budget monotonicity and fresh insertion.
Proof: Compare each real finite coordinate with the true larger finite supremum. -/
theorem maximalBudget_mono (ω η : Fin (N-1) → ℝ≥0) (h : ω≤η) : maximalBudget ω≤maximalBudget η := by
  apply Finset.sup_le
  intro i hi
  exact (h i).trans (Finset.le_sup (f := η) hi)

/-- Genuine componentwise budget enlargement preserves every actual increment and independent correction-defect scenario.
Use: Genuine componentwise budget enlargement preserves every actual increment and independent correction-defect scenario.
Article: main_krylov, s3:thm:cf, genuine source budget monotonicity and fresh insertion.
Proof: Use true individual spectral bounds and actual largest-budget monotonicity. -/
theorem scenarioBudget_mono (ω η : Fin (N-1) → ℝ≥0) (h : ω≤η) :
    scenarioBudget (n := n) N ω⊆scenarioBudget N η := by
  intro Θ hΘ
  constructor
  · intro i
    exact ⟨(hΘ.1 i).1,(hΘ.1 i).2.trans (by exact_mod_cast h i)⟩
  · intro i
    exact ⟨(hΘ.2 i).1,(hΘ.2 i).2.trans (by exact_mod_cast maximalBudget_mono ω η h)⟩

/-- Inserting a genuine feasible symmetric singleton increment into an actual zero slot preserves every true source budget and real correction defect.
Use: Inserting a genuine feasible symmetric singleton increment into an actual zero slot preserves every true source budget and real correction defect.
Article: main_krylov, s3:thm:cf, genuine source budget monotonicity and fresh insertion.
Proof: The actual modified slot has only the true inserted matrix, all other real increments are unchanged and genuine correction defects retain their actual bounds. -/
theorem scenarioBudget_add_single_of_zero (ω : Fin (N-1) → ℝ≥0) (Θ : CanonicalScenario n N)
    (hΘ : Θ∈scenarioBudget N ω) (l : Fin (N-1)) (hzero : Θ.1 l=0)
    (D : Matrix (Fin n) (Fin n) ℝ) (hD : D.IsSymm) (hn : ‖D‖≤(ω l : ℝ)) :
    Θ+(Pi.single l D,0)∈scenarioBudget N ω := by
  -- The genuine zero insertion slot prevents any actual triangle-inequality budget loss.
  classical
  constructor
  · intro i
    change (Θ.1 i+(Pi.single l D : Fin (N-1) → Matrix (Fin n) (Fin n) ℝ) i)∈symmetricMatrixBall (ω i)
    by_cases hi : i=l
    · subst i
      rw [Pi.single_eq_same,hzero,zero_add]
      exact ⟨hD,hn⟩
    · rw [Pi.single_eq_of_ne hi,add_zero]
      exact hΘ.1 i
  · intro i
    change Θ.2 i+0∈symmetricMatrixBall (maximalBudget ω)
    rw [add_zero]
    exact hΘ.2 i
end
end krylov.Envelope
