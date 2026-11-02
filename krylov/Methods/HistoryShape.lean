import krylov.Methods.CompiledProbed

/-!
Article: main_krylov, def:classes and lem:U, genuine structured history charts.
Use: preserve the actual iteration and correction-query boundaries in local
observed coefficient charts. Equal flattened lengths alone do not identify
those genuine boundaries. Compiled finite programs have a proved fixed true
query shape on every actual run, independently of operator and vector values.
Source: actual finite correction execution and elementary finite list lengths.
-/

namespace krylov.Methods
noncomputable section
open krylov.Stability
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual discrete query structure of a genuine history, with every correction-query count retained.
Use: The actual discrete query structure of a genuine history, with every correction-query count retained.
Article: main_krylov, def:classes and lem:U, genuine structured history charts.
Proof: Record the true correction-trace length at every actual iteration. -/
def History.queryShape (H : History E) : List ℕ := H.records.map fun r => r.corrections.length

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
/-- A genuine correction trace contributes precisely two true observed vectors per query.
Use: A genuine correction trace contributes precisely two true observed vectors per query.
Article: main_krylov, def:classes and lem:U, genuine structured history charts.
Proof: Induct on the actual query trace. -/
theorem correctionObservations_length (trace : List (E × E)) :
    (correctionObservations trace).length=2*trace.length := by
  induction trace with
  | nil => rfl
  | cons p trace ih =>
    simp only [correctionObservations,List.flatMap_cons,List.length_append,List.length_cons,List.length_nil] at ⊢
    change 2+(correctionObservations trace).length=2*(trace.length+1)
    rw [ih]
    omega

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
/-- The true finite observation count is determined by the genuine structured query history.
Use: The true finite observation count is determined by the genuine structured query history.
Article: main_krylov, def:classes and lem:U, genuine structured history charts.
Proof: Count the real current/initial gradients, four actual iteration vectors and two vectors per true correction query. -/
theorem History.observationList_length_shape (H : History E) :
    H.observationList.length=2+(H.queryShape.map (fun k => 4+2*k)).sum := by
  -- Keep the real correction boundaries while counting the actual flattened observations.
  rcases H with ⟨initial,records⟩
  induction records with
  | nil => rfl
  | cons r records ih =>
    simp only [History.observationList,History.queryShape,List.flatMap_cons,List.map_cons,
      List.length_cons,List.length_append,List.length_nil,List.sum_cons] at ⊢ ih
    change 4+(r.corrections.flatMap (fun p => [p.1,p.2])).length+
        (records.flatMap (fun r => [r.direction,r.probe,r.step,r.gradient]++r.corrections.flatMap (fun p => [p.1,p.2]))).length+1+1=_
    have ht := correctionObservations_length r.corrections
    dsimp only [correctionObservations] at ht
    omega

/-- The actual finite primitive correction program query count.
Use: The actual finite primitive correction program query count.
Article: main_krylov, def:classes and lem:U, genuine structured history charts.
Proof: Every genuine query constructor contributes one oracle observation pair. -/
def CorrectionProgram.queryCount {m : ℕ} : CorrectionProgram E m → ℕ
  | .done => 0
  | .query _ next => next.queryCount+1

/-- The true executed correction trace has exactly the primitive program query count.
Use: The true executed correction trace has exactly the primitive program query count.
Article: main_krylov, def:classes and lem:U, genuine structured history charts.
Proof: Induct on actual correction execution, retaining every real query and its returned gradient. -/
theorem CorrectionProgram.trace_length {m : ℕ} (P : CorrectionProgram E m)
    (B : E →L[ℝ] E) (g : E) (data : Fin m → E) :
    (runCorrections (P.tree data) B g).trace.length=P.queryCount := by
  induction P generalizing g with
  | done => rfl
  | query f next ih =>
    simpa only [CorrectionProgram.tree,runCorrections,List.length_cons,queryCount] using
      congrArg Nat.succ (ih (g+B (f.evaluate data)) (Fin.cons (g+B (f.evaluate data)) (Fin.cons (f.evaluate data) data)))

/-- A genuine compiled method advance prepends its actual primitive correction-query count to the true history structure.
Use: A genuine compiled method advance prepends its actual primitive correction-query count to the true history structure.
Article: main_krylov, def:classes and lem:U, genuine structured history charts.
Proof: Apply the actual finite correction trace-length identity to the real method advance. -/
theorem CompiledProbedPolicy.advance_queryShape (P : CompiledProbedPolicy E)
    (A B : E →L[ℝ] E) (H : History E) :
    (methodAdvance P.method A B H).queryShape=
      (P.correctionProgram H.observationList.length).queryCount::H.queryShape := by
  change (runCorrections _ B _).trace.length::H.queryShape=_
  rw [CompiledProbedPolicy.method,CorrectionProgram.trace_length]

/-- Every real execution of the same finite compiled method has the same genuine query structure at a fixed horizon.
Use: Every real execution of the same finite compiled method has the same genuine query structure at a fixed horizon.
Article: main_krylov, def:classes and lem:U, genuine structured history charts.
Proof: Induct on actual histories. Equal genuine prior shapes give the same true observation count and hence the same primitive correction program at the next actual step. -/
theorem CompiledProbedPolicy.run_queryShape (P : CompiledProbedPolicy E)
    (A B A' B' : ℕ → E →L[ℝ] E) (g g' : E) (N : ℕ) :
    (methodRun P.method A B g N).queryShape=(methodRun P.method A' B' g' N).queryShape := by
  -- Program selection uses the actual observation count, which is fixed by the true preceding shape.
  induction N with
  | zero => rfl
  | succ k ih =>
    rw [methodRun,methodRun,P.advance_queryShape,P.advance_queryShape]
    have hlen : (methodRun P.method A B g k).observationList.length=
        (methodRun P.method A' B' g' k).observationList.length := by
      rw [History.observationList_length_shape,History.observationList_length_shape,ih]
    rw [hlen,ih]
end
end krylov.Methods
