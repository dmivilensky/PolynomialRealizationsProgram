import krylov.Methods.FinalCorrection
import krylov.Methods.QuadraticCycles
import krylov.Methods.ExecutedFC

/-!
Article: main_krylov, def:classes and alg:fc, exact observed gradient accounting.
Use: count the actual initial observation, probes and every real adaptive
correction query, with explicit gate-dependent RFC counts.
Source: lengths of the actual executed query transcripts.
-/

namespace krylov.Methods
noncomputable section
open Matrix krylov.Reference
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
/-- The exact number of observed gradients in an actual probed history, including its initial observation.
Use: every real iteration has one probe and its recorded actual correction queries; no unevaluated output is counted.
Article: main_krylov, def:classes(M), gradient cost. -/
def probedCost (H : History E) : ℕ :=
  1+H.records.length+(H.records.map (fun r => r.corrections.length)).sum

/-- One actually executed probed iteration adds precisely its one probe and the queries in its real correction trace.
Use: cost follows from observations actually made, including finite adaptive correction trees.
Article: main_krylov, def:classes(M), exact per-iteration accounting.
Proof: the real new record contains exactly that actual correction trace. -/
theorem probedCost_advance (m : ProbedMethod E) (A B : E →L[ℝ] E) (H : History E) :
    probedCost (methodAdvance m A B H)=probedCost H+1+
      (runCorrections (m.correction H (A (m.direction H))) B
        (searchedGradient H.gradient (m.direction H) (A (m.direction H)))).trace.length := by
  change 1+(H.records.length+1)+(_+(H.records.map (fun r => r.corrections.length)).sum)=_
  unfold probedCost
  dsimp only
  omega

/-- The actual finite probed run has the exact sum of its genuine probe and correction observations.
Use: all gates and adaptive correction counts remain visible in the exact cost, rather than replaced by an assumed fixed work count.
Article: main_krylov, def:classes(M), total observed gradient count.
Proof: finite induction sums the proved exact actual iteration costs. -/
theorem probedCost_run (m : ProbedMethod E) (A B : ℕ → E →L[ℝ] E) (g : E) (N : ℕ) :
    probedCost (methodRun m A B g N)=1+N+
      ∑ k∈Finset.range N, (runCorrections
        (m.correction (methodRun m A B g k) (A k (m.direction (methodRun m A B g k)))) (B k)
        (searchedGradient (methodRun m A B g k).gradient (m.direction (methodRun m A B g k))
          (A k (m.direction (methodRun m A B g k))))).trace.length := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [methodRun,probedCost_advance,ih,Finset.sum_range_succ]
    omega

/-- The actual executed FC run costs exactly N+1 observed gradients.
Use: exact searches contribute their one real probe and there are no correction observations.
Article: main_krylov, def:classes and thm:A, FC observation count.
Proof: substitute the actually empty FC correction trace into the general exact count. -/
theorem fcCost_run (memory : ℕ → ℕ) (A : ℕ → E →L[ℝ] E) (g : E) (N : ℕ) :
    probedCost (fcHistory memory A g N)=N+1 := by
  change probedCost (methodRun (fcMethod memory) A A g N)=_
  rw [probedCost_run]
  simp only [fcMethod,retainedMethod,runCorrections,List.length_nil,Finset.sum_const_zero,add_zero,Nat.add_comm 1]

/-- The actual RFC correction phase makes exactly its prescribed count when its actual observed gate passes, and no correction queries otherwise.
Use: gate-dependent counts describe the real implemented RFC_k protocol on every operator sequence.
Article: main_krylov, alg:fc, observed-defect gate and repeat k_c times.
Proof: unfold the actual gate and apply the genuine repeated-query transcript count in its accepted branch. -/
theorem rfcCorrection_count (memory : ℕ → ℕ) (count : ℕ) (H : History E) (z : E)
    (B : E →L[ℝ] E) (g : E) :
    (runCorrections (rfcCorrection memory count H z) B g).trace.length=
      if selectedWindow memory H≠[] ∧ ‖windowDefect (selectedWindow memory H)‖<1 then count else 0 := by
  unfold rfcCorrection
  dsimp only
  split
  · exact repeatedModelTree_count _ _ B count _ g
  · rfl

/-- The actual fully evaluated RFC_k run has its exact accepted-gate correction cost.
Use: source gradient budgets use genuine observations; output-aware final correction elision removes exactly its separately proved last query.
Article: main_krylov, def:classes(M) and alg:fc, RFC_k oracle accounting.
Proof: substitute each actual gated correction trace length into the proved real run count. -/
theorem rfcCost_run (memory : ℕ → ℕ) (count : ℕ) (A B : ℕ → E →L[ℝ] E) (g : E) (N : ℕ) :
    probedCost (methodRun (rfcMethod memory count) A B g N)=1+N+
      ∑ k∈Finset.range N,
        if selectedWindow memory (methodRun (rfcMethod memory count) A B g k)≠[] ∧
          ‖windowDefect (selectedWindow memory (methodRun (rfcMethod memory count) A B g k))‖<1 then count else 0 := by
  rw [probedCost_run]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  exact rfcCorrection_count memory count _ _ _ _

end
end krylov.Methods
