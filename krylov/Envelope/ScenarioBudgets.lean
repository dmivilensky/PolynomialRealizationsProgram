import krylov.Envelope.ScenarioCoordinates
import Mathlib.Analysis.Normed.Module.FiniteDimension

set_option autoImplicit false
/-!
Article: main_krylov, thm:select, genuine compact canonical scenario budgets.
Use: define the actual independent symmetric spectral increment and
correction-defect budgets and prove real compactness and nonemptiness,
including every true zero-budget and empty finite-array case.
Source: standard finite-dimensional closed-ball compactness, actual
closed symmetry constraints and genuine product compactness.
-/

namespace krylov.Envelope
noncomputable section
open Matrix Set
open scoped BigOperators Matrix.Norms.L2Operator NNReal
variable {n N : ℕ}

/-- The actual symmetric finite-matrix spectral norm budget ball.
Use: The actual symmetric finite-matrix spectral norm budget ball.
Article: main_krylov, thm:select, genuine compact canonical scenario budgets.
Proof: Impose genuine transpose symmetry and the true nonnegative real spectral norm bound. -/
def symmetricMatrixBall (ω : ℝ≥0) : Set (Matrix (Fin n) (Fin n) ℝ) := {E | E.IsSymm ∧ ‖E‖≤(ω : ℝ)}

/-- Every actual symmetric spectral finite-matrix budget ball is genuinely compact.
Use: Every actual symmetric spectral finite-matrix budget ball is genuinely compact.
Article: main_krylov, thm:select, genuine compact canonical scenario budgets.
Proof: The genuine symmetry constraint is closed by true transpose continuity; intersect it with the actual compact finite-dimensional norm ball. -/
theorem symmetricMatrixBall_compact (ω : ℝ≥0) : IsCompact (symmetricMatrixBall (n := n) ω) := by
  -- The actual symmetry condition is closed, and the true spectral norm ball is compact in the genuine finite matrix space.
  have hs : IsClosed {E : Matrix (Fin n) (Fin n) ℝ | E.IsSymm} :=
    isClosed_eq continuous_id.matrix_transpose continuous_id
  have he : symmetricMatrixBall (n := n) ω=Metric.closedBall 0 (ω : ℝ) ∩ {E | E.IsSymm} := by
    ext E
    simp only [symmetricMatrixBall,mem_ofPred_eq,mem_inter_iff,Metric.mem_closedBall,dist_zero_right,and_comm]
  rw [he]
  exact (isCompact_closedBall 0 (ω : ℝ)).inter_right hs

/-- The genuine actual independent canonical increment budget profile.
Use: The genuine actual independent canonical increment budget profile.
Article: main_krylov, thm:select, genuine compact canonical scenario budgets.
Proof: Require every true finite increment to lie in its actual symmetric spectral budget ball. -/
def incrementBudget (N : ℕ) (ω : Fin (N-1) → ℝ≥0) : Set (Fin (N-1) → Matrix (Fin n) (Fin n) ℝ) :=
  {E | ∀ i, E i∈symmetricMatrixBall (ω i)}

/-- Every genuine finite canonical increment budget profile is actually compact.
Use: Every genuine finite canonical increment budget profile is actually compact.
Article: main_krylov, thm:select, genuine compact canonical scenario budgets.
Proof: Use real finite-product compactness of the true individual symmetric spectral balls. -/
theorem incrementBudget_compact (ω : Fin (N-1) → ℝ≥0) : IsCompact (incrementBudget (n := n) N ω) :=
  isCompact_pi_infinite (fun i => symmetricMatrixBall_compact (ω i))

/-- The true largest nonnegative finite canonical budget, with actual zero default for the empty array.
Use: The true largest nonnegative finite canonical budget, with actual zero default for the empty array.
Article: main_krylov, thm:select, genuine compact canonical scenario budgets.
Proof: Take the genuine finite nonnegative budget supremum. -/
def maximalBudget (ω : Fin (N-1) → ℝ≥0) : ℝ≥0 := Finset.univ.sup ω

/-- The actual full canonical increment and independent correction-defect budget set.
Use: The actual full canonical increment and independent correction-defect budget set.
Article: main_krylov, thm:select, genuine compact canonical scenario budgets.
Proof: Use genuine individual increment balls and the true largest increment budget for every actual correction defect. -/
def scenarioBudget (N : ℕ) (ω : Fin (N-1) → ℝ≥0) : Set (CanonicalScenario n N) :=
  incrementBudget N ω ×ˢ {F : Fin N → Matrix (Fin n) (Fin n) ℝ | ∀ k, F k∈symmetricMatrixBall (maximalBudget ω)}

/-- The genuine full finite canonical scenario budget set is actually compact.
Use: The genuine full finite canonical scenario budget set is actually compact.
Article: main_krylov, thm:select, genuine compact canonical scenario budgets.
Proof: Take the true product of the actual compact increment profile and genuine finite correction-defect balls. -/
theorem scenarioBudget_compact (ω : Fin (N-1) → ℝ≥0) : IsCompact (scenarioBudget (n := n) N ω) :=
  (incrementBudget_compact ω).prod (isCompact_pi_infinite (fun _ => symmetricMatrixBall_compact (maximalBudget ω)))

/-- The actual zero canonical scenario belongs to every genuine nonnegative source budget profile.
Use: The actual zero canonical scenario belongs to every genuine nonnegative source budget profile.
Article: main_krylov, thm:select, genuine compact canonical scenario budgets.
Proof: True zero increments and correction defects are symmetric and obey every actual nonnegative budget, including zero budgets. -/
theorem scenarioBudget_zero_mem (ω : Fin (N-1) → ℝ≥0) : (0 : CanonicalScenario n N)∈scenarioBudget N ω := by
  -- Genuine zero increments and real zero correction defects satisfy both actual independent budget families.
  constructor
  · intro i
    refine ⟨Matrix.isSymm_zero,?_⟩
    change ‖(0 : Matrix (Fin n) (Fin n) ℝ)‖≤(ω i : ℝ)
    rw [_root_.norm_zero]
    exact (ω i).coe_nonneg
  · intro k
    refine ⟨Matrix.isSymm_zero,?_⟩
    change ‖(0 : Matrix (Fin n) (Fin n) ℝ)‖≤(maximalBudget ω : ℝ)
    rw [_root_.norm_zero]
    exact (maximalBudget ω).coe_nonneg
end
end krylov.Envelope
