import krylov.Functions.ReferencePlaneSmallSource

/-!
Article: main_krylov, prop:Fcycle(iii), actual value-aware final policy.
Use: run the original gradient-only causal policy until the last search,
then allow one arbitrary data-only final correction. The information given
to that correction even includes all true searched line objectives. Source:
the actual scalar executor and the proved genuine cubic prefix replay.
-/
namespace krylov.Functions
noncomputable section
open krylov.Methods krylov.Reference krylov.Tensor krylov.Nonlinear
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The actual searched nodes before the final correction. The earlier
iterations execute every actual adaptive correction query; the last node
is obtained by a true scalar exact search. Article: prop:Fcycle(iii). -/
def scalarValueSearchNode (m : ProbedMethod E) (T : E ≃L[ℝ] E)
    (f : E → ℝ) (G : E → E) (R : ℝ) (x₀ : E) (N k : ℕ) : E :=
  if k<N then scalarFunctionPoint m T f G R x₀ k else
    let H := scalarFunctionRun m T f G R x₀ (N-1)
    metricLocalExactPoint T f (x₀+H.displacement) (m.direction H) R

/-- The genuine evaluated line displacement, before any correction at its
endpoint. The index is capped after the last retained pair only to make
the definition total. Article: prop:Fcycle(iii). -/
def scalarValueSearchStep (m : ProbedMethod E) (T : E ≃L[ℝ] E)
    (f : E → ℝ) (G : E → E) (R : ℝ) (x₀ : E) (N k : ℕ) : E :=
  let H := scalarFunctionRun m T f G R x₀ (min k (N-1))
  metricLocalExactPoint T f (x₀+H.displacement) (m.direction H) R-(x₀+H.displacement)

/-- Gather genuine sampled scalar/gradient data and the full true searched
line restrictions, before selecting the final correction. No unknown
derivative or future gradient is an input. Article: prop:Fcycle(iii). -/
def scalarValueTranscript (m : ProbedMethod E) (T : E ≃L[ℝ] E)
    (f : E → ℝ) (R : ℝ) (x₀ : E) (N : ℕ) : FunctionSearchTranscript E N :=
  functionSearchTranscript f
    (scalarValueSearchNode m T f (gradient f) R x₀ N)
    (scalarValueSearchStep m T f (gradient f) R x₀ N) N

/-- An arbitrary causal final output after the genuine original scalar
prefix. An original single final correction is the special policy
`fun H data => data.points last + correction H data`.
Article: main_krylov, prop:Fcycle(iii). -/
def scalarValueFinalOutput (m : ProbedMethod E) (T : E ≃L[ℝ] E)
    (f : E → ℝ) (R : ℝ) (x₀ : E) (N : ℕ)
    (policy : History E → FunctionSearchTranscript E N → E) : E :=
  policy (scalarFunctionRun m T f (gradient f) R x₀ (N-1))
    (scalarValueTranscript m T f R x₀ N)

variable {n : ℕ}

/-- Every actual searched node of any globally CG-consistent original
policy is its genuine reference node on the constructed scalar source.
This includes the last search, before the value-aware final correction.
Article: main_krylov, prop:Fcycle(iii). -/
theorem referencePlaneCubic_value_node (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hN : 2≤referenceAtomCount A hA g)
    (t : krylov.Tensor.BinaryCubic) (R : ℝ) (hH : ReferencePlanePositiveBall A hA g t R)
    (hnodes : ∀ i≤referenceAtomCount A hA g, ‖referencePlaneNode A g i‖≤R)
    (m : ProbedMethod (EuclideanSpace ℝ (Fin n))) (hm : CGConsistent m)
    (i : ℕ) (hi : i≤referenceAtomCount A hA g) :
    scalarValueSearchNode m (metricCoordinates A hA) (referencePlaneCubicObjective A hA g t)
      (gradient (referencePlaneCubicObjective A hA g t)) R 0 (referenceAtomCount A hA g) i=
      CG.displacement (cgOperator A) g i := by
  have hp := referencePlaneCubic_scalar_prefix A hA g hN t R hH hnodes m hm
  have hpos := cgOperator_positive A hA
  by_cases hit : i<referenceAtomCount A hA g
  · rw [scalarValueSearchNode,ite_eq_left hit,scalarFunctionPoint,hp i (by omega),zero_add]
    exact quadratic_displacement_eq_cg m hm _ hpos.1 hpos.2 g i
  · have hiN : i=referenceAtomCount A hA g := by omega
    rw [scalarValueSearchNode,ite_eq_right hit,hp _ (by omega)]
    dsimp only
    rw [zero_add]
    have hs := referencePlaneCubic_quadratic_search A hA g hN t R hH m hm
      (referenceAtomCount A hA g-1) (by omega) (hnodes _ (by omega))
    simpa only [show referenceAtomCount A hA g-1+1=referenceAtomCount A hA g by omega,hiN] using hs

/-- The actual evaluated search steps are the genuine physical CG steps,
as a conclusion of executing the true scalar searches.
Article: main_krylov, prop:Fcycle(iii). -/
theorem referencePlaneCubic_value_step (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hN : 2≤referenceAtomCount A hA g)
    (t : krylov.Tensor.BinaryCubic) (R : ℝ) (hH : ReferencePlanePositiveBall A hA g t R)
    (hnodes : ∀ i≤referenceAtomCount A hA g, ‖referencePlaneNode A g i‖≤R)
    (m : ProbedMethod (EuclideanSpace ℝ (Fin n))) (hm : CGConsistent m)
    (i : ℕ) (hi : i<referenceAtomCount A hA g) :
    scalarValueSearchStep m (metricCoordinates A hA) (referencePlaneCubicObjective A hA g t)
      (gradient (referencePlaneCubicObjective A hA g t)) R 0 (referenceAtomCount A hA g) i=
      referenceStep (cgOperator A) g i := by
  rw [scalarValueSearchStep,min_eq_left (show i≤referenceAtomCount A hA g-1 by omega),
    referencePlaneCubic_scalar_prefix A hA g hN t R hH hnodes m hm i (by omega)]
  rw [zero_add,referencePlaneCubic_quadratic_search A hA g hN t R hH m hm i hi (hnodes _ (by omega)),
    quadratic_displacement_eq_cg m hm _ (cgOperator_positive A hA).1 (cgOperator_positive A hA).2 g i,
    CG.displacement_succ,add_sub_cancel_left]
  rfl

set_option maxHeartbeats 800000 in
/-- The actual complete rich transcript of an executed original policy is
the reference-path transcript. It is derived from true execution, rather
than included in a class or source definition. Article: prop:Fcycle(iii). -/
theorem referencePlaneCubic_value_transcript (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hN : 2≤referenceAtomCount A hA g)
    (t : krylov.Tensor.BinaryCubic) (R : ℝ) (hH : ReferencePlanePositiveBall A hA g t R)
    (hnodes : ∀ i≤referenceAtomCount A hA g, ‖referencePlaneNode A g i‖≤R)
    (m : ProbedMethod (EuclideanSpace ℝ (Fin n))) (hm : CGConsistent m) :
    scalarValueTranscript m (metricCoordinates A hA) (referencePlaneCubicObjective A hA g t)
      R 0 (referenceAtomCount A hA g)=
      functionSearchTranscript (referencePlaneCubicObjective A hA g t)
        (CG.displacement (cgOperator A) g) (referenceStep (cgOperator A) g) (referenceAtomCount A hA g) := by
  apply FunctionSearchTranscript.ext
  · funext i
    exact referencePlaneCubic_value_node A hA g hN t R hH hnodes m hm i.val (by omega)
  · funext i
    exact referencePlaneCubic_value_step A hA g hN t R hH hnodes m hm i.val i.isLt
  · funext i
    exact congrArg (referencePlaneCubicObjective A hA g t)
      (referencePlaneCubic_value_node A hA g hN t R hH hnodes m hm i.val (by omega))
  · funext i
    exact congrArg (gradient (referencePlaneCubicObjective A hA g t))
      (referencePlaneCubic_value_node A hA g hN t R hH hnodes m hm i.val (by omega))
  · funext i α
    change referencePlaneCubicObjective A hA g t
      (scalarValueSearchNode m (metricCoordinates A hA) (referencePlaneCubicObjective A hA g t)
        (gradient (referencePlaneCubicObjective A hA g t)) R 0 (referenceAtomCount A hA g) i.val+
      α • scalarValueSearchStep m (metricCoordinates A hA) (referencePlaneCubicObjective A hA g t)
        (gradient (referencePlaneCubicObjective A hA g t)) R 0 (referenceAtomCount A hA g) i.val)=_
    rw [referencePlaneCubic_value_node A hA g hN t R hH hnodes m hm i.val (by omega),
      referencePlaneCubic_value_step A hA g hN t R hH hnodes m hm i.val i.isLt]
    rfl

end
end krylov.Functions
