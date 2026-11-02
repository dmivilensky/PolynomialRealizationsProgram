import krylov.Methods.CorrectionPairs
import krylov.Methods.InformationSpan
import krylov.Methods.HistoryShape

set_option autoImplicit false
/-!
Article: main_krylov, apB:lem:filtration, genuine intermediate correction observation geometry.
Use: retain the real span restrictions and zero-reference values of every
actual intermediate correction observation, not just their total movement.
Source: genuine finite nonanticipating correction execution, actual subspace
linearity and exact finite-list observation-coordinate identities.
-/

namespace krylov.Methods
noncomputable section
open Matrix
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Every genuine correction observation has its true query in the prescribed real span and its returned-gradient shift in the actual operator image of that span.
Use: Every genuine correction observation has its true query in the prescribed real span and its returned-gradient shift in the actual operator image of that span.
Article: main_krylov, apB:lem:filtration, genuine intermediate correction observation geometry.
Proof: Induct on the actual correction tree. Each real query lies in the true source span; cumulative returned-gradient shifts add actual operator images of those queries. -/
theorem correction_trace_mem (K : Submodule ℝ E) (q : CorrectionTree E) (B : E →L[ℝ] E) (g : E)
    (hq : q.InSubspace K) :
    ∀ p∈(runCorrections q B g).trace, p.1∈K ∧ p.2-g∈K.map B.toLinearMap := by
  -- Keep the actual cumulative gradient shift in the genuine image of the same true correction span.
  induction q generalizing g with
  | done => simp only [runCorrections,List.not_mem_nil,IsEmpty.forall_iff,implies_true]
  | query u next ih =>
    intro p hp
    change p∈(u,g+B u)::(runCorrections (next (g+B u)) B (g+B u)).trace at hp
    rcases List.mem_cons.mp hp with rfl|hp
    · refine ⟨hq.1,?_⟩
      change g+B u-g∈K.map B.toLinearMap
      rw [add_sub_cancel_left]
      exact Submodule.mem_map_of_mem hq.1
    · have ht := ih (g+B u) (g+B u) (hq.2 (g+B u)) p hp
      refine ⟨ht.1,?_⟩
      have hu : B u∈K.map B.toLinearMap := Submodule.mem_map_of_mem hq.1
      convert (K.map B.toLinearMap).add_mem ht.2 hu using 1
      abel

/-- On a genuine zero-query reference correction phase, every actual queried vector is zero and every actual intermediate gradient equals the true incoming gradient.
Use: On a genuine zero-query reference correction phase, every actual queried vector is zero and every actual intermediate gradient equals the true incoming gradient.
Article: main_krylov, apB:lem:filtration, genuine intermediate correction observation geometry.
Proof: Use the actual zero-correction predicate at each real oracle observation and propagate the unchanged genuine gradient through the finite tree. -/
theorem zeroCorrections_trace (q : CorrectionTree E) (B : E →L[ℝ] E) (g : E)
    (hz : ZeroCorrections q B g) : ∀ p∈(runCorrections q B g).trace, p.1=0 ∧ p.2=g := by
  induction q generalizing g with
  | done => simp only [runCorrections,List.not_mem_nil,IsEmpty.forall_iff,implies_true]
  | query u next ih =>
    -- The true zero query returns precisely the incoming observed gradient to the actual continuation.
    obtain ⟨hu,hnext⟩ := hz
    subst u
    simp only [map_zero,add_zero] at hnext
    intro p hp
    simp only [runCorrections,map_zero,add_zero] at hp
    rcases List.mem_cons.mp hp with rfl|hp
    · exact ⟨rfl,rfl⟩
    · exact ih g g hnext p hp

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
/-- Even actual flattened correction-observation coordinates are exactly the genuine queried displacement coordinates.
Use: Even actual flattened correction-observation coordinates are exactly the genuine queried displacement coordinates.
Article: main_krylov, apB:lem:filtration, genuine intermediate correction observation geometry.
Proof: Induct on the real trace and its actual list position, including genuine default coordinates outside the finite trace. -/
theorem correctionObservations_getD_even (trace : List (E × E)) (zero : E) (i : ℕ) :
    (trace.flatMap (fun p => [p.1,p.2])).getD (2*i) zero=(trace.getD i (zero,zero)).1 := by
  induction trace generalizing i with
  | nil => simp
  | cons p trace ih =>
    cases i with
    | zero => rfl
    | succ i =>
      simp only [List.flatMap_cons,List.cons_append,List.nil_append,show 2*(i+1)=2*i+2 by omega]
      simpa only [List.getD_cons_succ] using ih i

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
/-- Odd actual flattened correction-observation coordinates are exactly the genuine returned-gradient coordinates.
Use: Odd actual flattened correction-observation coordinates are exactly the genuine returned-gradient coordinates.
Article: main_krylov, apB:lem:filtration, genuine intermediate correction observation geometry.
Proof: Read the actual second coordinate at each true finite query position, preserving the real default outside the trace. -/
theorem correctionObservations_getD_odd (trace : List (E × E)) (zero : E) (i : ℕ) :
    (trace.flatMap (fun p => [p.1,p.2])).getD (2*i+1) zero=(trace.getD i (zero,zero)).2 := by
  induction trace generalizing i with
  | nil => simp
  | cons p trace ih =>
    cases i with
    | zero => rfl
    | succ i =>
      simp only [List.flatMap_cons,List.cons_append,List.nil_append,show 2*(i+1)+1=2*i+1+2 by omega]
      simpa only [List.getD_cons_succ] using ih i
end
end krylov.Methods
