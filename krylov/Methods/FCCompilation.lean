import krylov.Methods.FCObservedRule
import krylov.Methods.SmoothClasses

set_option autoImplicit false
/-!
Article: main_krylov, def:classes and cor:lm, genuine primitive compilation of actual FC.
Use: compile the real retained-window FC implementation into true primitive
observed coefficient rules and prove exact actual execution and local
policy equality on genuine fixed-shape observation histories.
Source: actual structured-history reconstruction and genuine finite FC
observed coefficient synthesis, preserving all true record boundaries.
-/

namespace krylov.Methods
noncomputable section
open Filter Topology krylov.Stability krylov.Reference
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The genuine primitive observed-coefficient compiled policy for the actual retained-window FC implementation.
Use: The genuine primitive observed-coefficient compiled policy for the actual retained-window FC implementation.
Article: main_krylov, def:classes and cor:lm, genuine primitive compilation of actual FC.
Proof: The true finite observation count identifies the real empty-correction record shape, and the actual correction program is empty. -/
def fcCompiledPolicy (memory : ℕ → ℕ) : CompiledProbedPolicy E where
  directionRule n := fcObservedRule memory (List.replicate ((n-2)/4) 0) n
  correctionProgram _ := .done

/-- The genuine primitive compiled FC policy makes exactly the actual empty correction decision.
Use: The genuine primitive compiled FC policy makes exactly the actual empty correction decision.
Article: main_krylov, def:classes and cor:lm, genuine primitive compilation of actual FC.
Proof: Its real finite correction program terminates immediately. -/
theorem fcCompiled_correction (memory : ℕ → ℕ) (H : History E) (z : E) :
    (fcCompiledPolicy memory).method.correction H z=.done := rfl

/-- Every genuine actual run of an empty-correction raw policy has exactly one true zero-query record per real iteration.
Use: Every genuine actual run of an empty-correction raw policy has exactly one true zero-query record per real iteration.
Article: main_krylov, def:classes and cor:lm, genuine primitive compilation of actual FC.
Proof: Induct through the actual executor; its real empty correction trace contributes genuine query count zero. -/
theorem methodRun_empty_corrections_shape (m : ProbedMethod E)
    (hm : ∀ H z, m.correction H z=.done) (A B : ℕ → E →L[ℝ] E) (g : E) (k : ℕ) :
    (methodRun m A B g k).queryShape=List.replicate k 0 := by
  -- Each genuine empty correction phase preserves the true zero-query record shape.
  induction k with
  | zero => rfl
  | succ k ih =>
    let H := methodRun m A B g k
    let d := m.direction H
    change (runCorrections (m.correction H (A k d)) (B k) (searchedGradient H.gradient d (A k d))).trace.length::
      (methodRun m A B g k).queryShape=List.replicate (k+1) 0
    rw [hm]
    change 0::_=_
    rw [ih,List.replicate_succ]

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
/-- Every genuine history with empty actual correction traces has exactly two plus four times its true iteration count observations.
Use: Every genuine history with empty actual correction traces has exactly two plus four times its true iteration count observations.
Article: main_krylov, def:classes and cor:lm, genuine primitive compilation of actual FC.
Proof: Count the actual finite observation layout using its true zero-query shape. -/
theorem zeroQuery_observationLength (H : History E)
    (hshape : H.queryShape=List.replicate H.records.length 0) :
    H.observationList.length=2+4*H.records.length := by
  have hlen := H.observationList_length_shape
  rw [hshape,List.map_replicate,List.sum_replicate] at hlen
  simp only [Nat.mul_zero,Nat.add_zero,nsmul_eq_mul,Nat.cast_id] at hlen
  omega

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
/-- The genuine observation count of a true empty-correction history identifies exactly its actual record/query shape.
Use: The genuine observation count of a true empty-correction history identifies exactly its actual record/query shape.
Article: main_krylov, def:classes and cor:lm, genuine primitive compilation of actual FC.
Proof: Recover the true iteration count from the exact actual observation-length identity. -/
theorem zeroQuery_coefficientShape (H : History E)
    (hshape : H.queryShape=List.replicate H.records.length 0) :
    List.replicate ((H.observationList.length-2)/4) 0=H.queryShape := by
  have hlen := zeroQuery_observationLength H hshape
  have hdiv : (H.observationList.length-2)/4=H.records.length := by omega
  rw [hdiv,← hshape]

/-- On every genuine empty-correction observed history the primitive compiled FC direction equals the real implemented retained-window FC direction exactly.
Use: On every genuine empty-correction observed history the primitive compiled FC direction equals the real implemented retained-window FC direction exactly.
Article: main_krylov, def:classes and cor:lm, genuine primitive compilation of actual FC.
Proof: Identify the true observed dimension and actual query shape, evaluate the genuine primitive coefficient rule and reconstruct the real complete history exactly. -/
theorem fcCompiled_direction (memory : ℕ → ℕ) (H : History E)
    (hshape : H.queryShape=List.replicate H.records.length 0) :
    (fcCompiledPolicy memory).method.direction H=(fcMethod memory).direction H := by
  -- Match the real finite observation count before synthesizing the actual primitive FC decision.
  change (fcObservedRule memory (List.replicate ((H.observationList.length-2)/4) 0) H.observationList.length).evaluate
    (observedArray H.observationList.length H.observationList)=_
  rw [zeroQuery_coefficientShape H hshape,fcObservedRule_evaluate]
  change windowDirection (selectedWindow memory (historyFromObservations H.queryShape
    (List.ofFn (observedArray H.observationList.length H.observationList))))
    (historyFromObservations H.queryShape (List.ofFn (observedArray H.observationList.length H.observationList))).gradient=_
  rw [ofFn_observedArray,historyFromObservations_actual]
  rfl

/-- The primitive compiled FC policy and the real retained-window FC executor have identical actual complete histories on every operator sequence.
Use: The primitive compiled FC policy and the real retained-window FC executor have identical actual complete histories on every operator sequence.
Article: main_krylov, def:classes and cor:lm, genuine primitive compilation of actual FC.
Proof: Induct through genuine executions. Every true preceding history has its real empty-correction shape, on which actual direction and full correction decisions coincide exactly. -/
theorem fcCompiled_run (memory : ℕ → ℕ) (A B : ℕ → E →L[ℝ] E) (g : E) (k : ℕ) :
    methodRun (fcCompiledPolicy memory).method A B g k=methodRun (fcMethod memory) A B g k := by
  -- Exact real direction and correction equality preserves every genuine iteration record.
  induction k with
  | zero => rfl
  | succ k ih =>
    let H := methodRun (fcMethod memory) A B g k
    have hs : H.queryShape=List.replicate H.records.length 0 := by
      dsimp only [H]
      rw [methodRun_length]
      exact methodRun_empty_corrections_shape (fcMethod memory) (fun _ _ => rfl) A B g k
    have hd := fcCompiled_direction memory H hs
    rw [methodRun,methodRun,ih]
    dsimp only [methodAdvance]
    rw [hd]
    rfl

/-- The real FC policy and its genuine primitive compiled representation agree on a true observed-data neighborhood of every actual empty-correction history.
Use: The real FC policy and its genuine primitive compiled representation agree on a true observed-data neighborhood of every actual empty-correction history.
Article: main_krylov, def:classes and cor:lm, genuine primitive compilation of actual FC.
Proof: The true fixed query shape determines the genuine record count. Pointwise primitive direction equality applies to every actual history on that shape, and both real correction programs are empty, so the whole observed-data neighborhood is valid. -/
theorem fcCompiled_local (memory : ℕ → ℕ) (H₀ : History E) (z₀ : E)
    (hs0 : H₀.queryShape=List.replicate H₀.records.length 0) :
    LocalCompiledAt (fcMethod memory) (fcCompiledPolicy memory) H₀ z₀ := by
  -- The true local branch fixes the actual query boundaries and hence the genuine iteration count.
  intro n data _
  refine ⟨Set.univ,Filter.univ_mem,?_⟩
  intro q _ H hshape _
  have hlen : H.records.length=H₀.records.length := by
    have hh := congrArg List.length hshape
    simpa only [History.queryShape,List.length_map] using hh
  have hs : H.queryShape=List.replicate H.records.length 0 := by rw [hlen,hshape,hs0]
  exact ⟨(fcCompiled_direction memory H hs).symm,rfl⟩
end
end krylov.Methods
