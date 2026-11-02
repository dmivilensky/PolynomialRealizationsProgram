import krylov.Methods.FCCompilation
import krylov.Methods.ObservedHistoryCharts

set_option autoImplicit false
/-!
Article: main_krylov, def:classes and cor:lm, reusable actual correction-free primitive compilation.
Use: transfer concrete finite observed coefficient rules into the true
primitive smooth source class for actual correction-free implementations.
Source: exact actual history reconstruction, true empty-query shape
and the existing genuine local compiled execution transfer.
-/

namespace krylov.Methods
noncomputable section
open Filter Topology krylov.Stability krylov.Reference
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The primitive compiled policy with a supplied finite observed direction rule and genuinely empty correction program.
Use: The primitive compiled policy with a supplied finite observed direction rule and genuinely empty correction program.
Article: main_krylov, def:classes and cor:lm, reusable actual correction-free primitive compilation.
Proof: The actual observation count identifies the true zero-query record shape. -/
def emptyCompiledPolicy (rule : (shape : List ℕ) → (n : ℕ) → ObservedRule E n) : CompiledProbedPolicy E where
  directionRule n := rule (List.replicate ((n-2)/4) 0) n
  correctionProgram _ := .done

/-- A concrete direction coefficient rule representing the actual reconstructed decision gives exact true compiled direction agreement on empty-correction histories.
Use: A concrete direction coefficient rule representing the actual reconstructed decision gives exact true compiled direction agreement on empty-correction histories.
Article: main_krylov, def:classes and cor:lm, reusable actual correction-free primitive compilation.
Proof: Recover the real query shape from the actual observation count and reconstruct the genuine complete history. -/
theorem emptyCompiled_direction (m : ProbedMethod E)
    (rule : (shape : List ℕ) → (n : ℕ) → ObservedRule E n)
    (hrule : ∀ shape n (data : Fin n → E), (rule shape n).evaluate data=m.direction (historyFromObservations shape (List.ofFn data)))
    (H : History E) (hshape : H.queryShape=List.replicate H.records.length 0) :
    (emptyCompiledPolicy rule).method.direction H=m.direction H := by
  change (rule (List.replicate ((H.observationList.length-2)/4) 0) H.observationList.length).evaluate
    (observedArray H.observationList.length H.observationList)=_
  rw [zeroQuery_coefficientShape H hshape,hrule,ofFn_observedArray,historyFromObservations_actual]

/-- An actual correction-free policy and its concrete observed direction compilation agree on a true fixed-shape observed-data neighborhood.
Use: An actual correction-free policy and its concrete observed direction compilation agree on a true fixed-shape observed-data neighborhood.
Article: main_krylov, def:classes and cor:lm, reusable actual correction-free primitive compilation.
Proof: Fixed real query boundaries determine actual record count; exact genuine direction agreement and both true empty correction programs hold throughout the whole observed chart. -/
theorem emptyCompiled_local (m : ProbedMethod E) (hm : ∀ H z, m.correction H z=.done)
    (rule : (shape : List ℕ) → (n : ℕ) → ObservedRule E n)
    (hrule : ∀ shape n (data : Fin n → E), (rule shape n).evaluate data=m.direction (historyFromObservations shape (List.ofFn data)))
    (H₀ : History E) (z₀ : E) (hs0 : H₀.queryShape=List.replicate H₀.records.length 0) :
    LocalCompiledAt m (emptyCompiledPolicy rule) H₀ z₀ := by
  -- The genuine fixed query shape determines the actual iteration count; the concrete direction identity applies on the whole true observed chart.
  intro n data _
  refine ⟨Set.univ,Filter.univ_mem,?_⟩
  intro q _ H hshape _
  have hlen : H.records.length=H₀.records.length := by
    have hh := congrArg List.length hshape
    simpa only [History.queryShape,List.length_map] using hh
  have hs : H.queryShape=List.replicate H.records.length 0 := by rw [hlen,hshape,hs0]
  exact ⟨(emptyCompiled_direction m rule hrule H hs).symm,hm _ _⟩

/-- Concrete genuine observed coefficient regularity on actual correction-free reference histories yields true primitive smooth-cycle membership of the real executor.
Use: Concrete genuine observed coefficient regularity on actual correction-free reference histories yields true primitive smooth-cycle membership of the real executor.
Article: main_krylov, def:classes and cor:lm, reusable actual correction-free primitive compilation.
Proof: Derive actual zero-query shapes, true local primitive policy agreement and exact compiled reference histories. Transfer the given genuine finite coefficient domains to those real compiled histories. -/
theorem emptyCompiled_smoothCycleAt (m : ProbedMethod E) (hm : ∀ H z, m.correction H z=.done)
    (rule : (shape : List ℕ) → (n : ℕ) → ObservedRule E n)
    (hrule : ∀ shape n (data : Fin n → E), (rule shape n).evaluate data=m.direction (historyFromObservations shape (List.ofFn data)))
    (Q : E →L[ℝ] E) (g : E) (N : ℕ) (r : WithTop ℕ∞)
    (hregular : ∀ k<N,
      let H := methodRun m (fun _ => Q) (fun _ => Q) g k
      ContDiffAt ℝ r (rule H.queryShape H.observationList.length).coefficient
        (observedArray H.observationList.length H.observationList)) :
    SmoothProbedCycleAt m r Q g N := by
  -- Identify genuine raw and compiled reference histories before transferring the actual finite coefficient regularity domains.
  let H := fun k => methodRun m (fun _ => Q) (fun _ => Q) g k
  let P := emptyCompiledPolicy rule
  have hs (k : ℕ) : (H k).queryShape=List.replicate (H k).records.length 0 := by
    rw [methodRun_length]
    exact methodRun_empty_corrections_shape m hm _ _ _ k
  have hl (k : ℕ) : LocalCompiledAt m P (H k) (Q (P.method.direction (H k))) :=
    emptyCompiled_local m hm rule hrule _ _ (hs k)
  have he (k : ℕ) : H k=methodRun P.method (fun _ => Q) (fun _ => Q) g k :=
    localCompiled_reference_run_of_raw m P _ _ g k (fun i _ => hl i)
  refine ⟨P,?_,?_⟩
  · intro k hk
    rw [← he k]
    constructor
    · change ContDiffAt ℝ r (rule (List.replicate (((H k).observationList.length-2)/4) 0)
        (H k).observationList.length).coefficient _
      rw [zeroQuery_coefficientShape (H k) (hs k)]
      exact hregular k hk
    · trivial
  · intro k _
    rw [← he k]
    exact hl k
end
end krylov.Methods
