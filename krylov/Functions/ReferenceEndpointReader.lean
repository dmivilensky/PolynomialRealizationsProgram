import krylov.Functions.EndpointValueReader
import krylov.Functions.ReferencePlaneObservedData
import krylov.Functions.ReferencePlaneNativePrefix

/-!
Article: main_krylov, thm:Fplanar, the actual endpoint-reader dictionary.
Use: reconstruct every endpoint, retained step and cached gradient from the
real chronological history. The current probe is a genuine observed secant,
and the final source wrapper derives its search step from the true source.
Source: original CG consistency, exact recorded histories and scalar source
observations. No external transcript reader or future derivative is assumed.
-/
namespace krylov.Functions
noncomputable section
open Finset krylov.Methods krylov.Reference krylov.Nonlinear krylov.Tensor
open scoped InnerProductSpace BigOperators Matrix.Norms.L2Operator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Every real history caches its genuine sequence of returned gradients
in reverse chronological storage order. Article: thm:Fplanar. -/
theorem methodRun_chronological_gradients (m : ProbedMethod E)
    (A B : ℕ → E →L[ℝ] E) (g : E) (k : ℕ) :
    (methodRun m A B g k).records.reverse.map IterationRecord.gradient=
      (List.range k).map (fun i=>(methodRun m A B g (i+1)).gradient) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change ((_ :: (methodRun m A B g k).records).reverse.map IterationRecord.gradient)=_
    rw [List.reverse_cons,List.map_append,ih,List.range_succ,List.map_append]
    rfl

/-- Every actual globally quadratic-consistent policy retains the genuine
complete CG step/secant history, including solved tails and arbitrary
positive direction scales. Article: thm:Fplanar, original cached data. -/
theorem quadratic_methodRun_pairs (m : ProbedMethod E) (hm : CGConsistent m)
    (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E,v≠0 → 0 < inner ℝ v (Q v)) (g : E) (k : ℕ) :
    (methodRun m (fun _=>Q) (fun _=>Q) g k).pairs=referencePairs Q g k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    obtain ⟨c,hc,hd,hzero⟩ := hm Q hQ hpos g k
    exact (reference_advance_scaled m Q g k _
      (quadratic_gradient_eq_cg m hm Q hQ hpos g k) ih hc.ne' hd hzero).2

/-- Reversing the actual reference pair cache gives the true chronological
physical step list. Article: thm:Fplanar, actual retained endpoints. -/
theorem referencePairs_chronological_steps (Q : E →L[ℝ] E) (g : E) (k : ℕ) :
    (referencePairs Q g k).reverse.map Prod.fst=(List.range k).map (referenceStep Q g) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [referencePairs,List.reverse_cons,List.map_append,List.map_cons,List.map_nil,
      List.range_succ,ih]

/-- Reading a genuine cached chronological step returns the actual CG step.
Article: main_krylov, thm:Fplanar. -/
theorem endpointPastStep_reference (H : History E) (Q : E →L[ℝ] E) (g : E) (k : ℕ)
    (hp : H.pairs=referencePairs Q g k) (i : ℕ) (hi : i<k) :
    endpointPastStep H i=referenceStep Q g i := by
  unfold endpointPastStep
  rw [←List.getElem?_map,hp,referencePairs_chronological_steps,List.getElem?_map,List.getElem?_range hi]
  rfl

/-- Every actual history retains the genuinely supplied initial gradient.
Article: main_krylov, thm:Fplanar, cached endpoint data. -/
theorem methodRun_initial_observation (m : ProbedMethod E)
    (A B : ℕ → E →L[ℝ] E) (g : E) (k : ℕ) : (methodRun m A B g k).initial=g := by
  induction k with
  | zero => rfl
  | succ k ih => exact ih

/-- Reading a genuine cached chronological gradient returns the actual CG
gradient, including the observed initial gradient at index zero.
Article: main_krylov, thm:Fplanar. -/
theorem endpointPastGradient_reference (m : ProbedMethod E) (hm : CGConsistent m)
    (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E,v≠0 → 0 < inner ℝ v (Q v)) (g : E) (k i : ℕ) (hi : i≤k) :
    endpointPastGradient (methodRun m (fun _=>Q) (fun _=>Q) g k) i=CG.gradient Q g i := by
  have hchron : (methodRun m (fun _=>Q) (fun _=>Q) g k).records.reverse.map IterationRecord.gradient=
      (List.range k).map (fun j=>CG.gradient Q g (j+1)) := by
    rw [methodRun_chronological_gradients]
    simp only [quadratic_gradient_eq_cg m hm Q hQ hpos g]
  by_cases hi₀ : i=0
  · subst i
    simp only [endpointPastGradient,ite_true]
    rw [methodRun_initial_observation]
    rfl
  · rw [endpointPastGradient,ite_eq_right hi₀,←List.getElem?_map,hchron,List.getElem?_map,
      List.getElem?_range (show i-1<k by omega)]
    simp only [Option.map_some,Option.getD_some,show i-1+1=i by omega]

/-- Cached original-reference steps and the actual current searched step
reconstruct every retained endpoint exactly. Article: thm:Fplanar. -/
theorem endpointReaderPoint_reference (m : ProbedMethod E) (hm : CGConsistent m)
    (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E,v≠0 → 0 < inner ℝ v (Q v)) (g : E) (N : ℕ) (hN : 0<N)
    (z : E) (hstep : endpointCurrentStep m (methodRun m (fun _=>Q) (fun _=>Q) g (N-1)) z=referenceStep Q g (N-1))
    (i : ℕ) (hi : i≤N) :
    endpointReaderPoint m N 0 (methodRun m (fun _=>Q) (fun _=>Q) g (N-1)) z i=CG.displacement Q g i := by
  have hp := quadratic_methodRun_pairs m hm Q hQ hpos g (N-1)
  by_cases hiN : i=N
  · subst i
    rw [endpointReaderPoint,ite_eq_left rfl,zero_add,
      quadratic_displacement_eq_cg m hm Q hQ hpos g,hstep]
    have hh := CG.displacement_succ Q g (N-1)
    simpa only [referenceStep,show N-1+1=N by omega] using! hh.symm
  · rw [endpointReaderPoint,ite_eq_right hiN,zero_add,CG.displacement]
    apply sum_congr rfl
    intro j hj
    exact endpointPastStep_reference _ Q g (N-1) hp j (by have hh := mem_range.mp hj; omega)

/-- The actual chronological reader keeps every true reference step,
including the final newly searched segment. Article: thm:Fplanar. -/
theorem endpointReaderStep_reference (m : ProbedMethod E) (hm : CGConsistent m)
    (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E,v≠0 → 0 < inner ℝ v (Q v)) (g : E) (N : ℕ)
    (z : E) (hstep : endpointCurrentStep m (methodRun m (fun _=>Q) (fun _=>Q) g (N-1)) z=referenceStep Q g (N-1))
    (i : ℕ) (hi : i<N) :
    endpointReaderStep m N (methodRun m (fun _=>Q) (fun _=>Q) g (N-1)) z i=referenceStep Q g i := by
  by_cases hiN : i+1=N
  · rw [endpointReaderStep,ite_eq_left hiN,hstep]
    congr 1
    omega
  · rw [endpointReaderStep,ite_eq_right hiN]
    exact endpointPastStep_reference _ Q g (N-1) (quadratic_methodRun_pairs m hm Q hQ hpos g (N-1)) i (by omega)

/-- A genuine observed secant ending at a stationary searched gradient
reconstructs exactly its real nonzero line length and endpoint gradient.
Article: main_krylov, thm:Fplanar, actual current-probe dictionary. -/
theorem lineLength_observed_stationary_secant (g d gnew : E) (α : ℝ)
    (hα : α≠0) (hg : inner ℝ d g≠0) (hnew : inner ℝ d gnew=0) :
    lineLength g d (α⁻¹ • (gnew-g))=α ∧
      searchedGradient g d (α⁻¹ • (gnew-g))=gnew := by
  have hline : lineLength g d (α⁻¹ • (gnew-g))=α := by
    simp only [lineLength,inner_smul_right,inner_sub_right,hnew,zero_sub]
    field_simp
  refine ⟨hline,?_⟩
  rw [searchedGradient,hline,smul_smul,mul_inv_cancel₀ hα,one_smul,add_sub_cancel]

variable {n : ℕ}

/-- The genuine last observed secant reconstructed from its already
observed searched gradient and the actual positive quadratic line scale.
This is a reference dictionary, not an extra argument to the value method.
Article: main_krylov, thm:Fplanar. -/
def referencePlaneEndpointProbe (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (t : krylov.Tensor.BinaryCubic)
    (m : ProbedMethod (EuclideanSpace ℝ (Fin n))) : EuclideanSpace ℝ (Fin n) :=
  let N := referenceAtomCount A hA g
  let H := methodRun m (fun _=>cgOperator A) (fun _=>cgOperator A) g (N-1)
  let α := lineLength H.gradient (m.direction H) (cgOperator A (m.direction H))
  α⁻¹ • (gradient (referencePlaneCubicObjective A hA g t)
    (CG.displacement (cgOperator A) g N)-H.gradient)

set_option maxHeartbeats 800000 in
/-- The last true source secant reproduces its exact actual reference step
and source searched gradient. Both identities are derived from genuine
source stationarity and positive CG search; they are not reader premises.
Article: main_krylov, thm:Fplanar, observed endpoint dictionary. -/
theorem referencePlaneEndpointProbe_search
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hN : 2≤referenceAtomCount A hA g)
    (t : krylov.Tensor.BinaryCubic) (m : ProbedMethod (EuclideanSpace ℝ (Fin n))) (hm : CGConsistent m) :
    let N := referenceAtomCount A hA g
    let H := methodRun m (fun _=>cgOperator A) (fun _=>cgOperator A) g (N-1)
    let z := referencePlaneEndpointProbe A hA g t m
    endpointCurrentStep m H z=referenceStep (cgOperator A) g (N-1) ∧
      searchedGradient H.gradient (m.direction H) z=
        gradient (referencePlaneCubicObjective A hA g t) (CG.displacement (cgOperator A) g N) := by
  let N := referenceAtomCount A hA g
  let Q := cgOperator A
  let H := methodRun m (fun _=>Q) (fun _=>Q) g (N-1)
  let d := m.direction H
  let α := lineLength H.gradient d (Q d)
  let f := referencePlaneCubicObjective A hA g t
  have hpos := cgOperator_positive A hA
  have hq := quadratic_search_positive m hm Q hpos.1 hpos.2 g (N-1)
    (cg_nonstagnation A hA g (N-1) (by dsimp only [N]; omega))
  have hα : 0<α := hq.2
  have hstep : α • d=referenceStep Q g (N-1) := scalar_quadratic_line_step m hm Q hpos.1 hpos.2 g (N-1)
  have hdg : inner ℝ d H.gradient≠0 := by
    intro hz
    have hh := hα
    simp only [α,lineLength,hz,neg_zero,zero_div] at hh
    exact (lt_irrefl 0) hh
  have hstat := referencePlaneCubic_search_stationary A hA g hN t (N-1) (by dsimp only [N]; omega)
    d α hα.ne' hstep
  have hpair := metricHilbertPlaneGradient_pair (metricCoordinates A hA) (referencePlane_metric_symmetric A hA)
    (referencePlaneFirst A g) (referencePlaneLast A hA g) (referencePlaneComplement A hA g)
    ‖canonicalCGStep A g 0‖ (referencePlaneRatio A hA g) t (CG.displacement Q g N) d
  change inner ℝ (gradient f (CG.displacement Q g N)) d=_ at hpair
  rw [←referencePlaneNode_metric] at hpair
  have hnew : inner ℝ d (gradient f (CG.displacement Q g N))=0 := by
    rw [real_inner_comm]
    apply hpair.trans
    simpa only [show N-1+1=N by dsimp only [N]; omega] using hstat
  have hline := lineLength_observed_stationary_secant H.gradient d (gradient f (CG.displacement Q g N)) α hα.ne' hdg hnew
  dsimp only
  change endpointCurrentStep m H (α⁻¹ • (gradient f (CG.displacement Q g N)-H.gradient))=_ ∧ _
  refine ⟨?_,hline.2⟩
  rw [endpointCurrentStep,hline.1]
  exact hstep

set_option maxHeartbeats 800000 in
/-- The concrete endpoint-only reader recovers every USED field of the
true scalar reference transcript: real points, actual retained steps,
actual scalar endpoint values and actual cached/search gradients.
Whole-line fields are deliberately absent: the reader never queries them.
Article: main_krylov, thm:Fplanar, genuine original-class information. -/
theorem referencePlaneEndpointReader_used_fields
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hN : 2≤referenceAtomCount A hA g)
    (t : krylov.Tensor.BinaryCubic) (m : ProbedMethod (EuclideanSpace ℝ (Fin n))) (hm : CGConsistent m) :
    let N := referenceAtomCount A hA g
    let f := referencePlaneCubicObjective A hA g t
    let H := methodRun m (fun _=>cgOperator A) (fun _=>cgOperator A) g (N-1)
    let z := referencePlaneEndpointProbe A hA g t m
    let data := endpointValueReader m N f 0 H z
    let reference := functionSearchTranscript f (CG.displacement (cgOperator A) g) (referenceStep (cgOperator A) g) N
    data.points=reference.points ∧ data.lineSteps=reference.lineSteps ∧
      data.values=reference.values ∧ data.gradients=reference.gradients := by
  let N := referenceAtomCount A hA g
  let Q := cgOperator A
  let f := referencePlaneCubicObjective A hA g t
  let H := methodRun m (fun _=>Q) (fun _=>Q) g (N-1)
  let z := referencePlaneEndpointProbe A hA g t m
  have hpos := cgOperator_positive A hA
  obtain ⟨hstep,hgrad⟩ := referencePlaneEndpointProbe_search A hA g hN t m hm
  have hp i (hi : i≤N) : endpointReaderPoint m N 0 H z i=CG.displacement Q g i :=
    endpointReaderPoint_reference m hm Q hpos.1 hpos.2 g N (by dsimp only [N]; omega) z hstep i hi
  have hs i (hi : i<N) : endpointReaderStep m N H z i=referenceStep Q g i :=
    endpointReaderStep_reference m hm Q hpos.1 hpos.2 g N z hstep i hi
  refine ⟨funext (fun i=>hp i.val (by omega)),funext (fun i=>hs i.val i.isLt),
    funext (fun i=>congrArg f (hp i.val (by omega))),?_⟩
  funext i
  change (if i.val=N then searchedGradient H.gradient (m.direction H) z else endpointPastGradient H i.val)=
    gradient f (CG.displacement Q g i.val)
  by_cases hiN : i.val=N
  · rw [ite_eq_left hiN,hiN]
    exact hgrad
  · rw [ite_eq_right hiN]
    rw [endpointPastGradient_reference m hm Q hpos.1 hpos.2 g (N-1) i.val (by omega)]
    exact (referencePlaneCubicGradient_prefix A hA g hN t i.val (by dsimp only [N] at *; omega)).symm

end
end krylov.Functions
