import krylov.OneGradient.ScenarioOperators
import Mathlib.Analysis.Calculus.ContDiff.Operations
set_option autoImplicit false
/-!
Article: main_krylov, thm:local, primitive original source operator calculus.
Use: native trajectory regularity starts from actual source base,
individual increments and independent output form in the full parameter.
Source: true finite physical source probe sums and exact output extension.
-/

namespace krylov.OneGradient
noncomputable section
open Matrix Finset krylov.Reference krylov.Secant krylov.Information
open scoped BigOperators Matrix.Norms.L2Operator
variable {p N : ℕ} {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Primitive C-one original physical source fields give C-one genuine
native query/output matrices on the full finite source parameter space.
Use: common source-wide remainders need no assumed smooth trajectory.
Article: main_krylov, thm:local, primitive full-source regularity.
Proof: each real probe is a finite sum of exactly the relevant original
increments; the true independent output form is added only after the probes. -/
theorem scenario_operators_contDiffAt (S : X → Scenario p)
    (hbase : ContDiffAt ℝ 1 (fun z => (S z).base) 0)
    (hinc : ∀ l<N,ContDiffAt ℝ 1 (fun z => (S z).increment l) 0)
    (hterm : ContDiffAt ℝ 1 (fun z => (S z).terminal) 0) (j : ℕ) :
    ContDiffAt ℝ 1 (fun z => oneGradientScenarioMatrices (S z) N j) 0 := by
  have hprobe (k : ℕ) (hk : k≤N) : ContDiffAt ℝ 1 (fun z => (S z).probe k) 0 :=
    hbase.add (ContDiffAt.sum (fun l hl => hinc l ((mem_range.mp hl).trans_le hk)))
  by_cases hj : j≤N
  · simpa only [oneGradientScenarioMatrices,ite_eq_left hj] using hprobe j hj
  · simpa only [oneGradientScenarioMatrices,ite_eq_right hj,Scenario.lastOperator] using
      (hprobe N le_rfl).add hterm

/-- Every genuine extended source matrix is symmetric from precisely
the original base, finite increment and independent output symmetries.
Use: arbitrary whole-source perturbation tuples feed native expansions.
Article: main_krylov, thm:local, primitive original source symmetry.
Proof: transpose each actual finite probe sum and add the true terminal form. -/
theorem scenario_operators_isSymm (S : Scenario p) (hbase : S.base.IsSymm)
    (hinc : ∀ l<N,(S.increment l).IsSymm) (hterm : S.terminal.IsSymm) (j : ℕ) :
    (oneGradientScenarioMatrices S N j).IsSymm := by
  have hprobe (k : ℕ) (hk : k≤N) : (S.probe k).IsSymm := hbase.add (by
    rw [Matrix.IsSymm,Matrix.transpose_sum]
    exact sum_congr rfl (fun l hl => (hinc l ((mem_range.mp hl).trans_le hk)).eq))
  by_cases hj : j≤N
  · rw [oneGradientScenarioMatrices_probe S N j hj]
    exact hprobe j hj
  · change (if j≤N then S.probe j else S.probe N+S.terminal).IsSymm
    rw [ite_eq_right hj]
    exact (hprobe N le_rfl).add hterm

/-- Zero true source increments and output form give the actual static
base at every extended native slot, including all post-output indices.
Use: actual native reference calibration is derived for full source tuples.
Article: main_krylov, thm:local, true full-source zero reference.
Proof: every actual probe sum is zero and the true terminal form is zero. -/
theorem scenario_operators_zero (S : Scenario p)
    (hinc : ∀ l<N,S.increment l=0) (hterm : S.terminal=0) (j : ℕ) :
    oneGradientScenarioMatrices S N j=S.base := by
  have hprobe (k : ℕ) (hk : k≤N) : S.probe k=S.base := by
    rw [Scenario.probe,sum_eq_zero (fun l hl => hinc l ((mem_range.mp hl).trans_le hk)),add_zero]
  by_cases hj : j≤N
  · rw [oneGradientScenarioMatrices_probe S N j hj,hprobe j hj]
  · simp only [oneGradientScenarioMatrices,ite_eq_right hj,Scenario.lastOperator,hprobe N le_rfl,hterm,add_zero]

end
end krylov.OneGradient
