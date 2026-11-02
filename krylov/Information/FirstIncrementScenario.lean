import krylov.Information.KnownBaseMidpointUpper
import krylov.Correction.ScenarioBounds

/-!
Article: main_krylov, thm:C2(c), original physical single-increment scenarios.
Use: realize arbitrary actual canonical first increments as genuine
known-base primitive source scenarios, with every original budget proved.
Source: actual positive-root congruence and exact finite source coordinates.
-/

namespace krylov.Information
noncomputable section
open Matrix Filter Asymptotics Topology Finset krylov.Reference krylov.Secant krylov.Envelope
  krylov.Correction krylov.Methods krylov.LinearAlgebra krylov.Stability krylov.Variation
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator
variable {n N : ℕ}

/-- The genuine physical source with known base, one canonical first increment and zero independent correction defects.
Use: supply actual physical known-base scenarios rather than hypothetical perturbed trajectories.
Article: main_krylov, thm:C2(c), actual single-increment physical source. -/
def firstIncrementScenario (A M : Matrix (Fin n) (Fin n) ℝ) : Scenario n where
  base := A
  increment := fun i => metricRoot A*firstIncrement M i*metricRoot A
  terminal := 0
  correction := fun _ => 0

/-- Every true symmetric first-increment matrix satisfying its primitive spectral budget gives an admissible original known-base source scenario.
Use: the ordinary RFC sharpness witness belongs to the exact physical source supremum.
Article: main_krylov, thm:C2(c), actual single-increment physical source.
Proof: positive-root congruence preserves symmetry and its inverse-root normalization recovers the exact primitive canonical increment. Every other original increment and independent correction defect is zero. -/
theorem firstIncrementScenario_admissible (A M : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.PosDef) (hM : M.IsSymm) (ω : ℝ) (hMn : ‖M‖≤ω) (N : ℕ) :
    (firstIncrementScenario A M).Admissible N A 0 (firstBudget ω) 0 0 := by
  -- Verify all original physical source budgets by exact canonical recovery.
  refine ⟨hA,?_,?_,Matrix.isSymm_zero,?_,?_⟩
  · simp only [firstIncrementScenario,sub_self,relativeBudget,relativeOperator,Matrix.mul_zero,Matrix.zero_mul,
      chebyshev1.opNorm,norm_zero,le_refl]
  · intro i _
    refine ⟨?_,?_⟩
    · change (metricRoot A*firstIncrement M i*metricRoot A).IsSymm
      have hi : (firstIncrement M i).IsSymm := by
        unfold firstIncrement
        split_ifs
        · exact hM
        · exact Matrix.isSymm_zero
      simp only [Matrix.IsSymm,transpose_mul,(metricRoot_isSymm A).eq,hi.eq,Matrix.mul_assoc]
    · change relativeBudget A (metricRoot A*firstIncrement M i*metricRoot A)≤firstBudget ω i
      change ‖relativeOperator A (metricRoot A*firstIncrement M i*metricRoot A)‖≤firstBudget ω i
      rw [← inverseRootForm A (firstIncrement M i) hA,relativeOperator_inverseRootForm A _ hA]
      unfold firstIncrement firstBudget
      split_ifs
      · exact hMn
      · simp only [norm_zero,le_refl]
  · simp only [firstIncrementScenario,relativeBudget,relativeOperator,Matrix.mul_zero,Matrix.zero_mul,
      chebyshev1.opNorm,norm_zero,le_refl]
  · intro i _
    exact ⟨Matrix.isSymm_zero,by simp only [firstIncrementScenario,relativeBudget,relativeOperator,Matrix.mul_zero,
      Matrix.zero_mul,chebyshev1.opNorm,norm_zero,le_refl]⟩

/-- The actual physical single-increment source has precisely the original first-increment sequence and zero terminal defect in its genuine canonical coordinates.
Use: apply the existing full finite-source cubic expansion to actual admissible physical witnesses.
Article: main_krylov, thm:C2(c), actual single-increment physical source.
Proof: on the true finite horizon, exact inverse-root transport recovers each original increment. Beyond it the genuine zero extension agrees with the one-increment sequence; the true terminal coordinate is zero. -/
theorem firstIncrementScenario_parameters (A M : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.PosDef) (hN : 0<N) :
    matrixSequenceExtension N ((firstIncrementScenario A M).canonicalParameters N).1=firstIncrement M ∧
    matrixSequenceExtension (N+1) ((firstIncrementScenario A M).canonicalParameters N).2 N=0 := by
  -- The actual finite source extension retains only the genuine first increment.
  constructor
  · funext i
    by_cases hi : i<N
    · rw [Scenario.canonicalParameters_increment _ N hi]
      change relativeOperator A (metricRoot A*firstIncrement M i*metricRoot A)=_
      rw [← inverseRootForm A (firstIncrement M i) hA,relativeOperator_inverseRootForm A _ hA]
    · have hz : i≠0 := by omega
      simp only [matrixSequenceExtension,dite_eq_right hi,firstIncrement,ite_eq_right hz]
  · rw [Scenario.canonicalParameters_correction _ N le_rfl]
    change relativeOperator A (if N<N then 0 else 0)=0
    simp only [ite_self,relativeOperator,Matrix.mul_zero,Matrix.zero_mul]

end
end krylov.Information
