import krylov.Methods.CorrectionFollow
import krylov.Methods.GenericReferencePairs

set_option autoImplicit false
/-!
Article: main_krylov, thm:select and apB:lem:mu(a), actual final latest-information correction wrapper.
Use: add one genuine final full-history model correction to the actual
executed method and retain a real globally CG-consistent continuation
after the designated cycle.
Source: genuine observed correction-tree continuation and the actual
full-memory FC continuation on the true updated pair transcript.
-/

namespace krylov.Methods
noncomputable section
open krylov.Reference
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- One actual latest-information correction on the true current direction, observed probe and full prior pair history.
Use: One actual latest-information correction on the true current direction, observed probe and full prior pair history.
Article: main_krylov, thm:select and apB:lem:mu(a), actual final latest-information correction wrapper.
Proof: Build the genuine augmented observed model and apply its real one-query correction to the actual incoming gradient. -/
def latestAfter (m : ProbedMethod E) (H : History E) (z gp : E) : CorrectionTree E :=
  let U := (m.direction H,z)::H.pairs
  repeatedModelTree (windowSteps U) (windowModel U) 1 gp

/-- The actual nonanticipating method obtained by appending one real latest-information correction at the designated final iteration and continuing by genuine full-memory FC afterwards.
Use: The actual nonanticipating method obtained by appending one real latest-information correction at the designated final iteration and continuing by genuine full-memory FC afterwards.
Article: main_krylov, thm:select and apB:lem:mu(a), actual final latest-information correction wrapper.
Proof: Use the original actual policy before the true horizon, attach the genuine full-model correction to its real terminal gradient, and read the actual updated pairs in every later FC decision. -/
def finalizedMethod (m : ProbedMethod E) (N : ℕ) : ProbedMethod E where
  direction H := if H.records.length<N then m.direction H else (fcMethod fullMemory).direction H
  correction H z :=
    if H.records.length+1=N then
      (m.correction H z).follow (latestAfter m H z) (searchedGradient H.gradient (m.direction H) z)
    else if H.records.length<N then m.correction H z else .done

/-- The actual finalized policy uses exactly the genuine original direction before its true horizon.
Use: The actual finalized policy uses exactly the genuine original direction before its true horizon.
Article: main_krylov, thm:select and apB:lem:mu(a), actual final latest-information correction wrapper.
Proof: Its real observed iteration count selects the original policy branch. -/
theorem finalizedMethod_direction_before (m : ProbedMethod E) (N : ℕ) (H : History E)
    (h : H.records.length<N) : (finalizedMethod m N).direction H=m.direction H := ite_eq_left h

/-- The actual finalized policy uses the genuine full-memory FC direction after its true designated horizon.
Use: The actual finalized policy uses the genuine full-memory FC direction after its true designated horizon.
Article: main_krylov, thm:select and apB:lem:mu(a), actual final latest-information correction wrapper.
Proof: The actual observed iteration count selects the real FC continuation. -/
theorem finalizedMethod_direction_after (m : ProbedMethod E) (N : ℕ) (H : History E)
    (h : N≤H.records.length) : (finalizedMethod m N).direction H=(fcMethod fullMemory).direction H :=
  ite_eq_right (by omega)

/-- Before the designated last iteration the actual finalized policy retains exactly the genuine original correction tree.
Use: Before the designated last iteration the actual finalized policy retains exactly the genuine original correction tree.
Article: main_krylov, thm:select and apB:lem:mu(a), actual final latest-information correction wrapper.
Proof: The true observed iteration count selects the unchanged original correction phase. -/
theorem finalizedMethod_correction_earlier (m : ProbedMethod E) (N : ℕ) (H : History E) (z : E)
    (h : H.records.length+1<N) : (finalizedMethod m N).correction H z=m.correction H z := by
  change (if H.records.length+1=N then _ else if H.records.length<N then _ else _)=_
  rw [ite_eq_right (by omega),ite_eq_left (by omega)]

/-- Every actual operator sequence has exactly the genuine original complete history before the true final correction horizon.
Use: Every actual operator sequence has exactly the genuine original complete history before the true final correction horizon.
Article: main_krylov, thm:select and apB:lem:mu(a), actual final latest-information correction wrapper.
Proof: Induct through actual executions; the true observed record count selects the genuine original direction and correction tree at every real earlier iteration. -/
theorem finalizedMethod_run_before (m : ProbedMethod E) (N : ℕ) (A B : ℕ → E →L[ℝ] E)
    (g : E) (k : ℕ) (hk : k<N) :
    methodRun (finalizedMethod m N) A B g k=methodRun m A B g k := by
  -- Every earlier real iteration uses the genuine original direction and correction tree, so the complete actual history is preserved.
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [methodRun,methodRun,ih (by omega)]
    unfold methodAdvance
    rw [finalizedMethod_direction_before m N _ (by rw [methodRun_length];omega)]
    dsimp only
    rw [finalizedMethod_correction_earlier m N (methodRun m A B g k) _ (by rw [methodRun_length];exact hk)]
end
end krylov.Methods
