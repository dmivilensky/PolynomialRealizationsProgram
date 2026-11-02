import krylov.Methods.TargetedFinalCorrection
import krylov.Methods.TargetedObservedProgram
import krylov.Methods.FCCompilation
import krylov.Methods.ObservedHistoryCharts

set_option autoImplicit false
/-!
Article: main_krylov, apB:prop:consist, actual reference-targeted primitive policy compilation.
Use: compile the genuine targeted method through its true final query using real observed FC directions and the actual target-relative full-model program.
Source: genuine empty-query-prefix observation counts, actual fixed-shape history reconstruction and the true target-relative model-program executor.
-/

namespace krylov.Methods
noncomputable section
open krylov.Reference krylov.Stability Filter Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The genuine primitive targeted policy selects its actual sole final target-relative model query from the true prefix observation count.
Use: The genuine primitive targeted policy selects its actual sole final target-relative model query from the true prefix observation count.
Article: main_krylov, apB:prop:consist, actual reference-targeted primitive policy compilation.
Proof: Use actual FC observed coefficients and the genuine fixed-shape targeted program. -/
def targetedCompiledPolicy (N : ℕ) (target : E) : CompiledProbedPolicy E where
  directionRule n := (fcCompiledPolicy fullMemory).directionRule n
  correctionProgram n := if (n-2)/4+1=N then
    targetedObservedProgram (List.replicate ((n-2)/4) 0) n target else .done

/-- On every actual zero-query-prefix history the genuine compiled direction is exactly full-memory FC.
Use: On every actual zero-query-prefix history the genuine compiled direction is exactly full-memory FC.
Article: main_krylov, apB:prop:consist, actual reference-targeted primitive policy compilation.
Proof: Reuse the true FC observed direction reconstruction. -/
theorem targetedCompiled_direction (N : ℕ) (target : E) (H : History E)
    (hshape : H.queryShape=List.replicate H.records.length 0) :
    (targetedCompiledPolicy N target).method.direction H=(fcMethod fullMemory).direction H :=
  fcCompiled_direction fullMemory H hshape

/-- The genuine compiled targeted program equals the actual raw target-relative correction decision on every true zero-query-prefix history.
Use: The genuine compiled targeted program equals the actual raw target-relative correction decision on every true zero-query-prefix history.
Article: main_krylov, apB:prop:consist, actual reference-targeted primitive policy compilation.
Proof: Recover the actual iteration count and complete pair window from real observations, then apply the genuine full-model program identity. -/
theorem targetedCompiled_correction (N : ℕ) (target : E) (H : History E) (z : E)
    (hshape : H.queryShape=List.replicate H.records.length 0) :
    (targetedCompiledPolicy N target).method.correction H z=(targetedFinalMethod N target).correction H z := by
  -- The genuine observation count identifies the actual record count before selecting the real target-model branch.
  have hd := targetedCompiled_direction N target H hshape
  have hdiv : (H.observationList.length-2)/4=H.records.length := by
    have hh := zeroQuery_observationLength H hshape
    omega
  change ((if (H.observationList.length-2)/4+1=N then _ else .done) :
    CorrectionProgram E (H.observationList.length+3)).tree
      (Fin.cons (searchedGradient H.gradient ((targetedCompiledPolicy N target).method.direction H) z)
        (Fin.cons z (Fin.cons ((targetedCompiledPolicy N target).method.direction H) _)))=_
  rw [hdiv,hd]
  by_cases he : H.records.length+1=N
  · rw [ite_eq_left he]
    change (targetedObservedProgram _ _ target).tree _=if H.records.length+1=N then _ else _
    rw [ite_eq_left he,targetedObservedProgram_tree,← hshape,
      chartWindow_of_array fullMemory H _ (ofFn_observedArray H.observationList).symm,selectedWindow_full]
    rfl
  · rw [ite_eq_right he]
    change CorrectionTree.done=if H.records.length+1=N then _ else _
    rw [ite_eq_right he]

/-- Before the true final query the actual primitive targeted executor has exactly the genuine FC history on arbitrary real operators.
Use: Before the true final query the actual primitive targeted executor has exactly the genuine FC history on arbitrary real operators.
Article: main_krylov, apB:prop:consist, actual reference-targeted primitive policy compilation.
Proof: Induct through real execution using actual zero-query history shapes and genuine primitive/raw decision equality. -/
theorem targetedCompiled_run_before (N : ℕ) (target : E) (A B : ℕ → E →L[ℝ] E)
    (g : E) (k : ℕ) (hk : k<N) :
    methodRun (targetedCompiledPolicy N target).method A B g k=
      methodRun (fcMethod fullMemory) A B g k := by
  -- Actual earlier branches make no queries, so their true fixed-shape coefficient rules reproduce every genuine FC record.
  induction k with
  | zero => rfl
  | succ k ih =>
    let H := methodRun (fcMethod fullMemory) A B g k
    have hs : H.queryShape=List.replicate H.records.length 0 := by
      dsimp only [H]
      rw [methodRun_length]
      exact methodRun_empty_corrections_shape (fcMethod fullMemory) (fun _ _ => rfl) A B g k
    have hd := targetedCompiled_direction N target H hs
    have hc := targetedCompiled_correction N target H (A k ((fcMethod fullMemory).direction H)) hs
    have he : (targetedCompiledPolicy N target).method.correction H (A k ((fcMethod fullMemory).direction H))=.done := by
      rw [hc]
      change (if H.records.length+1=N then _ else _)=_
      rw [show H.records.length=k from methodRun_length _ _ _ _ k,ite_eq_right (by omega)]
    rw [methodRun,methodRun,ih (by omega)]
    unfold methodAdvance
    change History.mk _ (_::_)=History.mk _ (_::_)
    rw [hd,he]
    rfl

/-- The actual raw targeted method and its genuine compiled policy agree on a true observed-data neighborhood of every real zero-query-prefix history.
Use: The actual raw targeted method and its genuine compiled policy agree on a true observed-data neighborhood of every real zero-query-prefix history.
Article: main_krylov, apB:prop:consist, actual reference-targeted primitive policy compilation.
Proof: The fixed actual query shape identifies the real record count; primitive and raw decisions agree on the entire true observation chart. -/
theorem targetedCompiled_local (N : ℕ) (target : E) (H₀ : History E) (z₀ : E)
    (hs0 : H₀.queryShape=List.replicate H₀.records.length 0) :
    LocalCompiledAt (targetedFinalMethod N target) (targetedCompiledPolicy N target) H₀ z₀ := by
  -- Fixing the real query shape fixes the genuine record count throughout the actual observed-data chart.
  intro n data _
  refine ⟨Set.univ,Filter.univ_mem,?_⟩
  intro q _ H hshape _
  have hlen : H.records.length=H₀.records.length := by
    have hh := congrArg List.length hshape
    simpa only [History.queryShape,List.length_map] using hh
  have hs : H.queryShape=List.replicate H.records.length 0 := by rw [hlen,hshape,hs0]
  exact ⟨(targetedCompiled_direction N target H hs).symm,(targetedCompiled_correction N target H q.2 hs).symm⟩
end
end krylov.Methods
