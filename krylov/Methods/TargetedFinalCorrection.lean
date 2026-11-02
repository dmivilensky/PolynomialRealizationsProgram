import krylov.Methods.FinalizedInformation
import krylov.Methods.CorrectionCount

set_option autoImplicit false
/-!
Article: main_krylov, apB:prop:consist, genuine reference-targeted final correction.
Use: construct an actual nonanticipating one-query full-memory policy aimed at a fixed prior gradient target and preserve its true FC prefix.
Source: actual retained FC direction, genuine observed latest-model basis and the proved physical inverse-model correction executor.
-/

namespace krylov.Methods
noncomputable section
open krylov.Reference
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- One actual full latest-model query corrects the true incoming gradient relative to a fixed prior target.
Use: One actual full latest-model query corrects the true incoming gradient relative to a fixed prior target.
Article: main_krylov, apB:prop:consist, genuine reference-targeted final correction.
Proof: Use only the actual augmented observed basis and latest pair model to synthesize the real correction. -/
def targetedCorrection (target : E) (H : History E) (z : E) : CorrectionTree E :=
  let d := (fcMethod fullMemory).direction H
  let U := (d,z)::H.pairs
  repeatedModelTree (windowSteps U) (windowModel U) 1 (searchedGradient H.gradient d z-target)

/-- The actual full-memory FC policy makes one genuine target-relative model correction only at its specified final iteration.
Use: The actual full-memory FC policy makes one genuine target-relative model correction only at its specified final iteration.
Article: main_krylov, apB:prop:consist, genuine reference-targeted final correction.
Proof: Select the real correction by actual record count and otherwise retain empty correction phases. -/
def targetedFinalMethod (N : ℕ) (target : E) : ProbedMethod E :=
  retainedMethod fullMemory (fun H z => if H.records.length+1=N then targetedCorrection target H z else .done)

/-- Every actual direction of the targeted policy is the genuine full-memory FC direction.
Use: Every actual direction of the targeted policy is the genuine full-memory FC direction.
Article: main_krylov, apB:prop:consist, genuine reference-targeted final correction.
Proof: The actual retained policy direction is unchanged by its correction rule. -/
theorem targetedFinalMethod_direction (N : ℕ) (target : E) (H : History E) :
    (targetedFinalMethod N target).direction H=(fcMethod fullMemory).direction H := rfl

/-- The actual targeted policy satisfies the genuine all-history full-memory information restriction.
Use: The actual targeted policy satisfies the genuine all-history full-memory information restriction.
Article: main_krylov, apB:prop:consist, genuine reference-targeted final correction.
Proof: Its real direction is FC and its sole possible correction is a true combination of the actual augmented observed basis. -/
theorem targetedFinalMethod_spanRestricted (N : ℕ) (target : E) :
    ProbedSpanRestricted fullMemory (targetedFinalMethod N target) := by
  -- The actual model query stays in the genuine full augmented observed span on every branch.
  intro H
  refine ⟨(fcMethod_spanRestricted fullMemory H).1,?_⟩
  intro z
  change CorrectionTree.InSubspace _ (if H.records.length+1=N then _ else _)
  by_cases h : H.records.length+1=N
  · rw [ite_eq_left h,selectedWindow_full]
    exact repeatedModelTree_inSubspace _ _ 1 _
  · rw [ite_eq_right h]
    trivial

/-- The actual targeted policy has at most one genuine correction on every real continuation branch.
Use: The actual targeted policy has at most one genuine correction on every real continuation branch.
Article: main_krylov, apB:prop:consist, genuine reference-targeted final correction.
Proof: The real final model tree has one query with an immediately terminating continuation. -/
theorem targetedFinalMethod_oneCorrection (N : ℕ) (target : E) :
    OneCorrectionMethod (targetedFinalMethod N target) := by
  intro H z
  change CorrectionsAtMostOne (if H.records.length+1=N then _ else _)
  split
  · intro _
    rfl
  · trivial

/-- Before its genuine final correction the actual targeted policy has exactly the complete FC history.
Use: Before its genuine final correction the actual targeted policy has exactly the complete FC history.
Article: main_krylov, apB:prop:consist, genuine reference-targeted final correction.
Proof: Induct through real executions; the observed record count selects the actual empty correction branch. -/
theorem targetedFinalMethod_run_before (N : ℕ) (target : E) (A B : ℕ → E →L[ℝ] E)
    (g : E) (k : ℕ) (hk : k<N) :
    methodRun (targetedFinalMethod N target) A B g k=methodRun (fcMethod fullMemory) A B g k := by
  -- Every genuine earlier correction branch is empty, so the actual complete FC prefix is preserved.
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [methodRun,methodRun,ih (by omega)]
    unfold methodAdvance
    change History.mk _ (_::_)=History.mk _ (_::_)
    simp only [targetedFinalMethod,retainedMethod,methodRun_length,ite_eq_right (show k+1≠N by omega),fcMethod]

/-- The actual targeted terminal gradient is exactly its true FC post-search gradient plus its real one-query target-relative model correction.
Use: The actual targeted terminal gradient is exactly its true FC post-search gradient plus its real one-query target-relative model correction.
Article: main_krylov, apB:prop:consist, genuine reference-targeted final correction.
Proof: Preserve the actual FC prefix and expand the genuine final observed correction execution. -/
theorem targetedFinalMethod_gradient_last (k : ℕ) (target : E) (A B : ℕ → E →L[ℝ] E) (g : E) :
    let H := methodRun (fcMethod fullMemory) A B g k
    let d := (fcMethod fullMemory).direction H
    let z := A k d
    let gp := searchedGradient H.gradient d z
    let U := (d,z)::H.pairs
    probedGradient (targetedFinalMethod (k+1) target) A B g (k+1)=
      gp+B k (combine (windowSteps U) (modelCoefficients (windowSteps U) (windowModel U) (gp-target))) := by
  dsimp only
  unfold probedGradient
  rw [methodRun,targetedFinalMethod_run_before (k+1) target A B g k (by omega)]
  unfold methodAdvance
  dsimp only [targetedFinalMethod,retainedMethod]
  rw [methodRun_length,ite_eq_left rfl]
  rfl
end
end krylov.Methods
