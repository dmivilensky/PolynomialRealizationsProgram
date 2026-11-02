import krylov.Methods.FinalizedReference
import krylov.Methods.AppendedModelObserved
import krylov.Methods.HistoryShapeSelection
import krylov.Methods.ObservedHistoryCharts

set_option autoImplicit false
/-!
Article: main_krylov, thm:select and apB:lem:mu(a), genuine final-wrapper primitive compilation.
Use: compile the actual final latest-information wrapper with its true
original observed programs and genuine subsequent full-memory FC charts,
preserving all real query boundaries and whole correction decisions.
Source: actual observed-dimension history-shape selection and the true
appended full-model coefficient program and observed FC reconstruction.
-/

namespace krylov.Methods
noncomputable section
open krylov.Reference krylov.Stability
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The genuine primitive finite observed policy for an actual final latest-model wrapper and its true full-memory FC continuation.
Use: The genuine primitive finite observed policy for an actual final latest-model wrapper and its true full-memory FC continuation.
Article: main_krylov, thm:select and apB:lem:mu(a), genuine final-wrapper primitive compilation.
Proof: Select real reference query shapes solely by actual observed dimension; retain original programs before the horizon, append the genuine final model query, then use actual FC coefficients and empty corrections. -/
def finalizedCompiledPolicy (P : CompiledProbedPolicy E) (N : ℕ) (reference : ℕ → History E) : CompiledProbedPolicy E where
  directionRule n :=
    let shape := selectedHistoryShape reference n
    if shape.length<N then P.directionRule n else fcObservedRule fullMemory shape n
  correctionProgram n :=
    let shape := selectedHistoryShape reference n
    if shape.length+1=N then appendedModelObserved (P.correctionProgram n) shape
    else if shape.length<N then P.correctionProgram n else .done

/-- Before the true horizon, the genuine compiled wrapper direction is exactly the actual original compiled direction.
Use: Before the true horizon, the genuine compiled wrapper direction is exactly the actual original compiled direction.
Article: main_krylov, thm:select and apB:lem:mu(a), genuine final-wrapper primitive compilation.
Proof: Its true selected history shape has the actual record count, which selects the genuine original primitive rule. -/
theorem finalizedCompiled_direction_before (P : CompiledProbedPolicy E) (N : ℕ) (reference : ℕ → History E)
    (H : History E) (hshape : selectedHistoryShape reference H.observationList.length=H.queryShape)
    (hk : H.records.length<N) :
    (finalizedCompiledPolicy P N reference).method.direction H=P.method.direction H := by
  change (if (selectedHistoryShape reference H.observationList.length).length<N then P.directionRule H.observationList.length else _).evaluate _=_
  rw [hshape,show H.queryShape.length=H.records.length by simp only [History.queryShape,List.length_map],ite_eq_left hk]
  rfl

/-- After the true horizon, the genuine compiled wrapper direction is exactly the actual full-memory FC direction on the real structured history.
Use: After the true horizon, the genuine compiled wrapper direction is exactly the actual full-memory FC direction on the real structured history.
Article: main_krylov, thm:select and apB:lem:mu(a), genuine final-wrapper primitive compilation.
Proof: Use the actual selected query shape and genuine observed FC reconstruction. -/
theorem finalizedCompiled_direction_after (P : CompiledProbedPolicy E) (N : ℕ) (reference : ℕ → History E)
    (H : History E) (hshape : selectedHistoryShape reference H.observationList.length=H.queryShape)
    (hk : N≤H.records.length) :
    (finalizedCompiledPolicy P N reference).method.direction H=(fcMethod fullMemory).direction H := by
  change (if (selectedHistoryShape reference H.observationList.length).length<N then _ else fcObservedRule fullMemory
    (selectedHistoryShape reference H.observationList.length) H.observationList.length).evaluate _=_
  rw [hshape,show H.queryShape.length=H.records.length by simp only [History.queryShape,List.length_map],ite_eq_right (by omega)]
  exact fcObservedRule_of_array fullMemory H _ (ofFn_observedArray H.observationList).symm

/-- Every genuine earlier compiled wrapper correction is exactly the actual original compiled correction tree.
Use: Every genuine earlier compiled wrapper correction is exactly the actual original compiled correction tree.
Article: main_krylov, thm:select and apB:lem:mu(a), genuine final-wrapper primitive compilation.
Proof: The true record count selects the real original program, with its actual unchanged direction and post-search input. -/
theorem finalizedCompiled_correction_earlier (P : CompiledProbedPolicy E) (N : ℕ) (reference : ℕ → History E)
    (H : History E) (z : E) (hshape : selectedHistoryShape reference H.observationList.length=H.queryShape)
    (hk : H.records.length+1<N) :
    (finalizedCompiledPolicy P N reference).method.correction H z=P.method.correction H z := by
  -- Select the real original primitive direction before identifying the actual unchanged earlier correction program.
  have hd := finalizedCompiled_direction_before P N reference H hshape (by omega)
  have hp : (finalizedCompiledPolicy P N reference).correctionProgram H.observationList.length=P.correctionProgram H.observationList.length := by
    change (if (selectedHistoryShape reference H.observationList.length).length+1=N then _ else if _ then _ else _)=_
    rw [hshape,show H.queryShape.length=H.records.length by simp only [History.queryShape,List.length_map],
      ite_eq_right (by omega),ite_eq_left (by omega)]
  change ((finalizedCompiledPolicy P N reference).correctionProgram H.observationList.length).tree
    (Fin.cons (searchedGradient H.gradient ((finalizedCompiledPolicy P N reference).method.direction H) z)
      (Fin.cons z (Fin.cons ((finalizedCompiledPolicy P N reference).method.direction H) _)))=_
  rw [hp,hd]
  rfl

/-- At the genuine final iteration, the actual compiled wrapper correction tree is exactly the original real compiled tree followed by one genuine full observed latest-model query.
Use: At the genuine final iteration, the actual compiled wrapper correction tree is exactly the original real compiled tree followed by one genuine full observed latest-model query.
Article: main_krylov, thm:select and apB:lem:mu(a), genuine final-wrapper primitive compilation.
Proof: Select the actual appended observed program, identify its true original direction and synthesize the genuine full-history model basis for every real future returned gradient. -/
theorem finalizedCompiled_correction_last (P : CompiledProbedPolicy E) (N : ℕ) (reference : ℕ → History E)
    (H : History E) (z : E) (hshape : selectedHistoryShape reference H.observationList.length=H.queryShape)
    (hk : H.records.length+1=N) :
    (finalizedCompiledPolicy P N reference).method.correction H z=
      (P.method.correction H z).follow (latestAfter P.method H z) (searchedGradient H.gradient (P.method.direction H) z) := by
  have hd := finalizedCompiled_direction_before P N reference H hshape (by omega)
  -- The genuine final observed program retains the true full original basis through every actual original correction answer.
  have hp : (finalizedCompiledPolicy P N reference).correctionProgram H.observationList.length=
      appendedModelObserved (P.correctionProgram H.observationList.length) H.queryShape := by
    change (if (selectedHistoryShape reference H.observationList.length).length+1=N then _ else _)=_
    rw [hshape,show H.queryShape.length=H.records.length by simp only [History.queryShape,List.length_map],ite_eq_left hk]
  change ((finalizedCompiledPolicy P N reference).correctionProgram H.observationList.length).tree
    (Fin.cons (searchedGradient H.gradient ((finalizedCompiledPolicy P N reference).method.direction H) z)
      (Fin.cons z (Fin.cons ((finalizedCompiledPolicy P N reference).method.direction H) _)))=_
  rw [hp,hd,appendedModelObserved_tree,chartWindow_of_array fullMemory H _ (ofFn_observedArray H.observationList).symm,selectedWindow_full]
  rfl

/-- After the true horizon, the genuine compiled wrapper correction phase stops without an actual query.
Use: After the true horizon, the genuine compiled wrapper correction phase stops without an actual query.
Article: main_krylov, thm:select and apB:lem:mu(a), genuine final-wrapper primitive compilation.
Proof: Both real program branch conditions fail at the actual observed iteration count. -/
theorem finalizedCompiled_correction_after (P : CompiledProbedPolicy E) (N : ℕ) (reference : ℕ → History E)
    (H : History E) (z : E) (hshape : selectedHistoryShape reference H.observationList.length=H.queryShape)
    (hk : N≤H.records.length) : (finalizedCompiledPolicy P N reference).method.correction H z=.done := by
  change ((if (selectedHistoryShape reference H.observationList.length).length+1=N then _ else if _ then _ else _)
    : CorrectionProgram E (H.observationList.length+3)).tree _=.done
  rw [hshape,show H.queryShape.length=H.records.length by simp only [History.queryShape,List.length_map],
    ite_eq_right (by omega),ite_eq_right (by omega)]
  rfl


/-- Actual local original direction and whole-tree agreement imply genuine pointwise agreement of the real wrapper and its primitive compiled policy before the true horizon.
Use: Actual local original direction and whole-tree agreement imply genuine pointwise agreement of the real wrapper and its primitive compiled policy before the true horizon.
Article: main_krylov, thm:select and apB:lem:mu(a), genuine final-wrapper primitive compilation.
Proof: Use actual preserved earlier decisions; at the real final iteration the appended full-model finish depends on exactly the same genuine direction, observed probe and pair transcript. -/
theorem finalizedCompiled_matches_before (m : ProbedMethod E) (P : CompiledProbedPolicy E)
    (N : ℕ) (reference : ℕ → History E) (H : History E) (z : E)
    (hshape : selectedHistoryShape reference H.observationList.length=H.queryShape)
    (hk : H.records.length<N)
    (hmatch : m.direction H=P.method.direction H ∧ m.correction H z=P.method.correction H z) :
    (finalizedMethod m N).direction H=(finalizedCompiledPolicy P N reference).method.direction H ∧
    (finalizedMethod m N).correction H z=(finalizedCompiledPolicy P N reference).method.correction H z := by
  -- True original whole-tree agreement transfers through the genuine appended model query for every actual future returned gradient.
  constructor
  · rw [finalizedMethod_direction_before m N H hk,finalizedCompiled_direction_before P N reference H hshape hk]
    exact hmatch.1
  · by_cases he : H.records.length+1=N
    · rw [finalizedCompiled_correction_last P N reference H z hshape he]
      change (if H.records.length+1=N then _ else _)=_
      rw [ite_eq_left he]
      rw [hmatch.1,hmatch.2]
      have hf : latestAfter m H z=latestAfter P.method H z := by
        funext v
        unfold latestAfter
        rw [hmatch.1]
      rw [hf]
    · have hearly : H.records.length+1<N := by omega
      rw [finalizedMethod_correction_earlier m N H z hearly,finalizedCompiled_correction_earlier P N reference H z hshape hearly]
      exact hmatch.2

/-- The actual wrapper and its genuine primitive compiler agree pointwise on all real directions and correction trees after the true horizon.
Use: The actual wrapper and its genuine primitive compiler agree pointwise on all real directions and correction trees after the true horizon.
Article: main_krylov, thm:select and apB:lem:mu(a), genuine final-wrapper primitive compilation.
Proof: Both actual directions are genuine full-memory FC and both true correction phases stop. -/
theorem finalizedCompiled_matches_after (m : ProbedMethod E) (P : CompiledProbedPolicy E)
    (N : ℕ) (reference : ℕ → History E) (H : History E) (z : E)
    (hshape : selectedHistoryShape reference H.observationList.length=H.queryShape)
    (hk : N≤H.records.length) :
    (finalizedMethod m N).direction H=(finalizedCompiledPolicy P N reference).method.direction H ∧
    (finalizedMethod m N).correction H z=(finalizedCompiledPolicy P N reference).method.correction H z := by
  constructor
  · rw [finalizedMethod_direction_after m N H hk,finalizedCompiled_direction_after P N reference H hshape hk]
  · rw [finalizedCompiled_correction_after P N reference H z hshape hk]
    change (if H.records.length+1=N then _ else if H.records.length<N then _ else _)=(CorrectionTree.done : CorrectionTree E)
    rw [ite_eq_right (by omega),ite_eq_right (by omega)]

end
end krylov.Methods
