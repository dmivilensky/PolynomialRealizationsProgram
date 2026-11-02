import krylov.Functions.ScalarValueFinalExecution

/-!
Article: main_krylov, prop:Fcycle(iii), causal actual scalar information fibre.
Use: every globally CG-consistent original prefix followed by an arbitrary
data-only final correction has identical actual output on the true binary
value fibre. All searches, zero intermediate corrections, sampled gradients
and complete searched objectives come from actual scalar execution.
Source: the proved actual reference replay and invisible polynomial fibre.
-/
namespace krylov.Functions
noncomputable section
open krylov.Methods krylov.Reference krylov.Tensor krylov.Nonlinear krylov.Tensor.BinaryCubic krylov.Correction
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {n : ℕ}

/-- The true physical reference step is exactly transported to its actual
canonical CG step. Article: main_krylov, prop:Fcycle(iii). -/
theorem referencePlaneStep_metric (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (i : ℕ) :
    metricCoordinates A hA (referenceStep (cgOperator A) g i)=canonicalCGStep A g i := by
  rw [metricCoordinates_apply]
  rfl

/-- Equality of the exact binary observations gives equality of every
actual reference-path sampled value, gradient and whole search objective.
Article: main_krylov, prop:Fcycle(iii). -/
theorem referencePlaneCubic_reference_transcript_equal (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hN : 2≤referenceAtomCount A hA g)
    (t u : krylov.Tensor.BinaryCubic) (hobs : observe (referencePlaneRatio A hA g) t=observe (referencePlaneRatio A hA g) u) :
    functionSearchTranscript (referencePlaneCubicObjective A hA g u)
      (CG.displacement (cgOperator A) g) (referenceStep (cgOperator A) g) (referenceAtomCount A hA g)=
    functionSearchTranscript (referencePlaneCubicObjective A hA g t)
      (CG.displacement (cgOperator A) g) (referenceStep (cgOperator A) g) (referenceAtomCount A hA g) := by
  obtain ⟨_,_,_,_,_,hpoints,hlines⟩ := referencePlane_sample_lines A hA g hN
  apply metricHilbertPlaneObjective_transcript_equal (metricCoordinates A hA)
    (referencePlane_metric_symmetric A hA) (referencePlaneFirst A g) (referencePlaneLast A hA g)
    (referencePlaneComplement A hA g) ‖canonicalCGStep A g 0‖ (referencePlaneRatio A hA g) t u hobs
  · intro i hi
    rw [←referencePlaneNode_metric]
    exact hpoints i hi
  · intro i hi
    rw [←referencePlaneNode_metric,referencePlaneStep_metric]
    exact hlines i hi

/-- Every bit of the genuinely executed rich scalar transcript is the
same on the original value fibre. True query paths and true gradients
are consequences of global CG consistency and actual Hessian positivity.
Article: main_krylov, prop:Fcycle(iii). -/
theorem referencePlaneCubic_actual_transcript_equal (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hN : 2≤referenceAtomCount A hA g)
    (t u : krylov.Tensor.BinaryCubic) (R : ℝ)
    (ht : ReferencePlanePositiveBall A hA g t R) (hu : ReferencePlanePositiveBall A hA g u R)
    (hnodes : ∀ i≤referenceAtomCount A hA g, ‖referencePlaneNode A g i‖≤R)
    (hobs : observe (referencePlaneRatio A hA g) t=observe (referencePlaneRatio A hA g) u)
    (m : ProbedMethod (EuclideanSpace ℝ (Fin n))) (hm : CGConsistent m) :
    scalarValueTranscript m (metricCoordinates A hA) (referencePlaneCubicObjective A hA g u)
      R 0 (referenceAtomCount A hA g)=
    scalarValueTranscript m (metricCoordinates A hA) (referencePlaneCubicObjective A hA g t)
      R 0 (referenceAtomCount A hA g) := by
  rw [referencePlaneCubic_value_transcript A hA g hN u R hu hnodes m hm,
    referencePlaneCubic_value_transcript A hA g hN t R ht hnodes m hm]
  exact referencePlaneCubic_reference_transcript_equal A hA g hN t u hobs

/-- Any actual data-only final output following an arbitrary original
globally CG-consistent scalar prefix is identical on the value fibre.
The output has no boundedness, regularity or preassigned location premise.
Article: main_krylov, prop:Fcycle(iii), all-method causal reduction. -/
theorem referencePlaneCubic_final_output_equal (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hN : 2≤referenceAtomCount A hA g)
    (t u : krylov.Tensor.BinaryCubic) (R : ℝ)
    (ht : ReferencePlanePositiveBall A hA g t R) (hu : ReferencePlanePositiveBall A hA g u R)
    (hnodes : ∀ i≤referenceAtomCount A hA g, ‖referencePlaneNode A g i‖≤R)
    (hobs : observe (referencePlaneRatio A hA g) t=observe (referencePlaneRatio A hA g) u)
    (m : ProbedMethod (EuclideanSpace ℝ (Fin n))) (hm : CGConsistent m)
    (policy : History (EuclideanSpace ℝ (Fin n)) →
      FunctionSearchTranscript (EuclideanSpace ℝ (Fin n)) (referenceAtomCount A hA g) → EuclideanSpace ℝ (Fin n)) :
    scalarValueFinalOutput m (metricCoordinates A hA) (referencePlaneCubicObjective A hA g u)
      R 0 (referenceAtomCount A hA g) policy=
    scalarValueFinalOutput m (metricCoordinates A hA) (referencePlaneCubicObjective A hA g t)
      R 0 (referenceAtomCount A hA g) policy := by
  unfold scalarValueFinalOutput
  rw [referencePlaneCubic_scalar_prefix A hA g hN u R hu hnodes m hm _ le_rfl,
    referencePlaneCubic_scalar_prefix A hA g hN t R ht hnodes m hm _ le_rfl,
    referencePlaneCubic_actual_transcript_equal A hA g hN t u R ht hu hnodes hobs m hm]

/-- Multiplying the genuine tensor by a common scalar preserves its exact
observed coefficient fibre. Article: main_krylov, prop:Fcycle(iii). -/
theorem scaleBinaryCubic_observe_equal (r α : ℝ) (t u : krylov.Tensor.BinaryCubic)
    (hobs : observe r t=observe r u) :
    observe r (scaleBinaryCubic α t)=observe r (scaleBinaryCubic α u) := by
  have h0 := congrArg Observation.t0 hobs
  have hP := congrArg Observation.P hobs
  have h3 := congrArg Observation.t3 hobs
  change t.t0=u.t0 at h0
  change t.t1+r*t.t2=u.t1+r*u.t2 at hP
  change t.t3=u.t3 at h3
  change (⟨α*t.t0,α*t.t1+r*(α*t.t2),α*t.t3⟩ : Observation)=
    ⟨α*u.t0,α*u.t1+r*(α*u.t2),α*u.t3⟩
  congr 1
  · exact congrArg (α*·) h0
  · linear_combination α*hP
  · exact congrArg (α*·) h3

/-- On every sufficiently small genuine source, any actual original
CG-consistent scalar prefix with an arbitrary data-only final correction
has identical output throughout the true value fibre. The common search
domain and every native reference admission are derived uniformly from
the primitive source; they are absent from this theorem's assumptions.
Article: main_krylov, prop:Fcycle(iii), complete causal class reduction. -/
theorem referencePlane_small_source_final_output_equal
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hN : 2≤referenceAtomCount A hA g)
    (U : ℝ) (hU : 0<U) :
    ∃ R ep : ℝ, 0<R ∧ 0<ep ∧ ∀ ε : ℝ, 0<ε → ε<ep → ∀ α : ℝ, 0≤α → α≤U →
      ∀ t u : krylov.Tensor.BinaryCubic, t.InBall → u.InBall →
      observe (referencePlaneRatio A hA g) t=observe (referencePlaneRatio A hA g) u →
      ∀ m : ProbedMethod (EuclideanSpace ℝ (Fin n)), CGConsistent m →
      ∀ policy : History (EuclideanSpace ℝ (Fin n)) →
        FunctionSearchTranscript (EuclideanSpace ℝ (Fin n)) (referenceAtomCount A hA (ε • g)) → EuclideanSpace ℝ (Fin n),
      scalarValueFinalOutput m (metricCoordinates A hA)
          (referencePlaneCubicObjective A hA (ε • g) (scaleBinaryCubic α u))
          R 0 (referenceAtomCount A hA (ε • g)) policy=
        scalarValueFinalOutput m (metricCoordinates A hA)
          (referencePlaneCubicObjective A hA (ε • g) (scaleBinaryCubic α t))
          R 0 (referenceAtomCount A hA (ε • g)) policy := by
  obtain ⟨R,ep,hR,hep,hdom⟩ := referencePlane_small_source_domain A hA g hN U hU
  refine ⟨R,ep,hR,hep,?_⟩
  intro ε hε heps α hα hαU t u ht hu hobs m hm policy
  have htD := hdom ε hε heps α hα hαU t ht
  have huD := hdom ε hε heps α hα hαU u hu
  apply referencePlaneCubic_final_output_equal A hA (ε • g)
    (by rwa [referenceAtomCount_scalar A hA g ε hε.ne'])
    (scaleBinaryCubic α t) (scaleBinaryCubic α u) R htD.1 huD.1 htD.2 _ m hm policy
  rw [referencePlaneRatio_scalar A hA g hε]
  exact scaleBinaryCubic_observe_equal _ α t u hobs

end
end krylov.Functions
