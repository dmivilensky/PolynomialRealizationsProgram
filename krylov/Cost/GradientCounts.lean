import krylov.Methods.RFCFinalOutput
import krylov.Methods.OneGradient

/-!
Article: main_krylov, thm:hier and tab:s1-ladder.
Use: count actual gradient observations, including the initial gradient,
every true probe and evaluated correction, and the unevaluated final output.
The RFC count is gate dependent; `2n-1` is its maximal count and is exact
when every noninitial gate accepts. Exact line searches are counted as one
gradient probe in this oracle model, not as an implementation complexity.
Source: lengths of the actual previously verified execution transcripts.
-/

namespace krylov.Cost
noncomputable section
open krylov.Methods krylov.Reference Finset
open scoped BigOperators Matrix.Norms.L2Operator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual observed gate at iteration k of the one-correction RFC run. -/
def rfcGate (memory : ℕ → ℕ) (A B : ℕ → E →L[ℝ] E) (g : E) (k : ℕ) : Prop :=
  let H := methodRun (rfcMethod memory 1) A B g k
  selectedWindow memory H ≠ [] ∧ ‖windowDefect (selectedWindow memory H)‖ < 1

instance rfcGate_decidable (memory : ℕ → ℕ) (A B : ℕ → E →L[ℝ] E) (g : E) (k : ℕ) :
    Decidable (rfcGate memory A B g k) := by
  unfold rfcGate
  infer_instance

theorem rfcGate_zero (memory : ℕ → ℕ) (A B : ℕ → E →L[ℝ] E) (g : E) :
    ¬rfcGate memory A B g 0 := by
  simp [rfcGate, methodRun, selectedWindow, History.pairs, recordPairs]

/-- The number of real observations when the final correction is returned
without querying its gradient. The zero-step history has just its input. -/
def rfcOutputCost (memory : ℕ → ℕ) (A B : ℕ → E →L[ℝ] E) (g : E) : ℕ → ℕ
  | 0 => 1
  | k + 1 =>
    let H := methodRun (rfcMethod memory 1) A B g k
    let d := (rfcMethod memory 1).direction H
    let z := A k d
    let r := runFinalCorrections (rfcFinalPhase memory 1 H z) (B k)
      (searchedGradient H.gradient d z)
    probedCost H + 1 + r.trace.length

/-- One-correction RFC has no terminal correction observation: its final
point is the same genuine semantic output as in the evaluated execution. -/
theorem rfcOutputCost_succ (memory : ℕ → ℕ) (A B : ℕ → E →L[ℝ] E) (g : E) (k : ℕ) :
    rfcOutputCost memory A B g (k + 1) =
      2 + k + ∑ j ∈ range k, if rfcGate memory A B g j then 1 else 0 := by
  dsimp only [rfcOutputCost, rfcMethod, retainedMethod]
  rw [rfcFinalPhase_count]
  simp only [Nat.sub_self, ite_self, Nat.add_zero]
  change probedCost (methodRun (rfcMethod memory 1) A B g k) + 1 = _
  have hc := rfcCost_run memory 1 A B g k
  change probedCost (methodRun (rfcMethod memory 1) A B g k) =
    1 + k + ∑ j ∈ range k, if rfcGate memory A B g j then 1 else 0 at hc
  omega

/-- The maximal source RFC count holds on every actual operator sequence,
including skipped gates and solved or degenerate histories. -/
theorem rfcOutputCost_le (memory : ℕ → ℕ) (A B : ℕ → E →L[ℝ] E) (g : E)
    (n : ℕ) (hn : 2 ≤ n) : rfcOutputCost memory A B g n ≤ 2 * n - 1 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  rw [rfcOutputCost_succ]
  have hk : 0 < k := by omega
  have he : (∑ j ∈ range k, if rfcGate memory A B g j then 1 else 0) ≤ k - 1 := by
    have ht : (∑ j ∈ range k, if rfcGate memory A B g j then 1 else 0) =
        ∑ j ∈ range (k - 1), if rfcGate memory A B g (j + 1) then 1 else 0 := by
      conv_lhs => rw [show k = k - 1 + 1 by omega, sum_range_succ']
      simp only [rfcGate_zero, ite_false, Nat.add_zero]
    rw [ht]
    calc
      _ ≤ ∑ _j ∈ range (k - 1), (1 : ℕ) := sum_le_sum fun _ _ ↦ by split_ifs <;> omega
      _ = k - 1 := by simp
  omega

/-- The printed `2n-1` count is attained exactly when the genuine
noninitial gates in the evaluated prefix all accept. -/
theorem rfcOutputCost_eq (memory : ℕ → ℕ) (A B : ℕ → E →L[ℝ] E) (g : E)
    (n : ℕ) (hn : 2 ≤ n) (hgate : ∀ k, 0 < k → k < n - 1 → rfcGate memory A B g k) :
    rfcOutputCost memory A B g n = 2 * n - 1 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  rw [rfcOutputCost_succ]
  have hk : 0 < k := by omega
  have he : (∑ j ∈ range k, if rfcGate memory A B g j then 1 else 0) = k - 1 := by
    conv_lhs => rw [show k = k - 1 + 1 by omega, sum_range_succ']
    have hh (j : ℕ) (hj : j ∈ range (k - 1)) : rfcGate memory A B g (j + 1) :=
      hgate _ (by omega) (by have := mem_range.mp hj; omega)
    simp only [rfcGate_zero, ite_false, Nat.add_zero]
    rw [sum_congr rfl (fun j hj ↦ ite_eq_left (hh j hj))]
    simp
  omega

/-- FC's exact source count includes its final observed gradient. -/
theorem fc_cycle_gradients (memory : ℕ → ℕ) (A : ℕ → E →L[ℝ] E) (g : E) (n : ℕ) :
    probedCost (fcHistory memory A g n) = n + 1 := fcCost_run memory A g n

/-- Every actual one-gradient policy, in particular both XRFC bases,
uses exactly n+1 observations; its virtual output adds no query. -/
theorem oneGradient_cycle_gradients (m : OneGradientMethod E)
    (A : ℕ → E →L[ℝ] E) (g : E) (n : ℕ) :
    oneGradientCost (oneGradientRun m A g n) = n + 1 := oneGradientCost_run m A g n

end
end krylov.Cost
