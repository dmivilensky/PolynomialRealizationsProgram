import krylov.Functions.EndpointCentreExecution
import krylov.Functions.ReferenceEndpointReader
import krylov.Functions.NativeCentreUpper

/-!
Article: main_krylov, thm:Fplanar, complete endpoint-grounded native witness.
Use: identify the true final gradient-query point of the globally admitted
endpoint-only method with the attaining centre, and prove the sharp uniform
small-source bound. Every reader field, search point and current probe is
derived from actual scalar execution. No reader agreement, trajectory,
output location or remainder is assumed.
Source: true CG scalar replay and the concrete cached endpoint dictionary.
-/
namespace krylov.Functions
noncomputable section
open krylov.Methods krylov.Reference krylov.Tensor krylov.Nonlinear krylov.Correction krylov.Tensor.BinaryCubic
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {n : ℕ}

set_option maxHeartbeats 800000 in
/-- The actual globally admitted endpoint-only method queries precisely
the finite centre output on every genuine constructed scalar source.
Its reader and probe identities follow from true cached history and exact
scalar search; no reader-matching premise appears. Article: thm:Fplanar. -/
theorem referencePlaneCubic_endpoint_global_eq_output
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hN : 2≤referenceAtomCount A hA g)
    (t : krylov.Tensor.BinaryCubic) (R : ℝ) (hH : ReferencePlanePositiveBall A hA g t R)
    (hnodes : ∀ i≤referenceAtomCount A hA g, ‖referencePlaneNode A g i‖≤R) (B : ℝ) :
    let f := referencePlaneCubicObjective A hA g t
    let S := metricCoordinates A hA
    let hpos : 0<referenceAtomCount A hA g := by omega
    scalarFunctionPoint (budgetedCentreEndpointMethod S B hpos f 0) S f (gradient f) R 0 (referenceAtomCount A hA g)=
      (budgetedCentreValueMethod S B hpos).output hpos S f R 0 := by
  dsimp only
  let N := referenceAtomCount A hA g
  let Q := cgOperator A
  let S := metricCoordinates A hA
  let f := referencePlaneCubicObjective A hA g t
  let m := (fcMethod fullMemory : ProbedMethod (EuclideanSpace ℝ (Fin n)))
  let M := budgetedCentreValueMethod S B (show 0<N by omega)
  let H := methodRun m (fun _=>Q) (fun _=>Q) g (N-1)
  let d := m.direction H
  let α := lineLength H.gradient d (Q d)
  let y := CG.displacement Q g N
  let z := referencePlaneEndpointProbe A hA g t m
  let data := endpointValueReader m N f 0 H z
  let ref := functionSearchTranscript f (CG.displacement Q g) (referenceStep Q g) N
  have hpos := cgOperator_positive A hA
  have hα : 0<α := (quadratic_search_positive m fullFC_consistent Q hpos.1 hpos.2 g (N-1)
    (cg_nonstagnation A hA g (N-1) (by dsimp only [N]; omega))).2
  have hstep : α • d=referenceStep Q g (N-1) := scalar_quadratic_line_step m fullFC_consistent Q hpos.1 hpos.2 g (N-1)
  have hx : H.displacement=CG.displacement Q g (N-1) := quadratic_displacement_eq_cg m fullFC_consistent Q hpos.1 hpos.2 g (N-1)
  have hd : d≠0 := by
    intro hz
    have hh := (quadratic_search_positive m fullFC_consistent Q hpos.1 hpos.2 g (N-1)
      (cg_nonstagnation A hA g (N-1) (by dsimp only [N]; omega))).1
    change 0 < inner ℝ d (Q d) at hh
    rw [hz,inner_zero_left] at hh
    exact (lt_irrefl 0) hh
  have hraw : y-H.displacement=α • d := by
    have hnext := CG.displacement_succ Q g (N-1)
    rw [show N-1+1=N by omega] at hnext
    change CG.displacement Q g N=CG.displacement Q g (N-1)+referenceStep Q g (N-1) at hnext
    change CG.displacement Q g N-H.displacement=_
    rw [hx,hnext,add_sub_cancel_left]
    exact hstep.symm
  have hobs : observedLineParameter d (y-H.displacement)=α := by
    rw [hraw]
    exact observedLineParameter_smul d α hd
  have hpre : scalarFunctionRun m S f (gradient f) R 0 (N-1)=H :=
    referencePlaneCubic_scalar_prefix A hA g hN t R hH hnodes m fullFC_consistent _ le_rfl
  have hy : metricLocalExactPoint S f H.displacement d R=y := by
    have hs := referencePlaneCubic_quadratic_search A hA g hN t R hH m fullFC_consistent (N-1)
      (by dsimp only [N]; omega) (hnodes _ (by dsimp only [N]; omega))
    simpa only [show N-1+1=N by omega] using hs
  have hout := M.endpoint_global_output (show 0<N by omega) S f (gradient f) R 0 (N-1) (by omega)
  dsimp only [M,budgetedCentreValueMethod] at hout
  rw [hpre,zero_add,hy,hobs] at hout
  change scalarFunctionPoint (M.globalMethod (by omega) (endpointValueReader m N f 0)) S f (gradient f) R 0 (N-1+1)=
    y+observedSpanFinalCorrection (by omega)
      (metricPlaneResponseCoefficients (budgetedPlaneCentreOutput B) S (by omega)) H data at hout
  rw [show N-1+1=N by omega] at hout
  obtain ⟨_,hs,hv,hg⟩ := referencePlaneEndpointReader_used_fields A hA g hN t m fullFC_consistent
  have hc := metricPlaneResponseCorrection_endpoint_congr (budgetedPlaneCentreOutput B) S (show 0<N by omega) H data ref hs hv hg
  rw [hc] at hout
  rw [OneCorrectionValueMethod.output_reference A hA g hN t R hH hnodes]
  change scalarFunctionPoint (M.globalMethod (by omega) (endpointValueReader m N f 0)) S f (gradient f) R 0 N=
    y+observedSpanFinalCorrection (by omega)
      (metricPlaneResponseCoefficients (budgetedPlaneCentreOutput B) S (by omega)) H ref
  exact hout

set_option maxHeartbeats 800000 in
/-- A concrete endpoint-grounded globally CG-consistent original method
attains the sharp function-value coefficient on all sufficiently small
actual scalar sources. The global method, actual search and cached-value
reader are the executed objects; all data identities are conclusions.
Article: main_krylov, thm:Fplanar, full native class upper witness. -/
theorem nativeEndpointCentre_gradient_upper
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hN : 2≤referenceAtomCount A hA g) (B : ℝ) (hB : 0<B) :
    ∃ R ep C : ℝ, 0<R ∧ 0<ep ∧ 0<C ∧
      ∀ (ε : ℝ) (hε : 0<ε), ε<ep → ∀ t : krylov.Tensor.BinaryCubic, t.InBall →
      let p := ε*‖canonicalCGStep A g 0‖
      let r := referencePlaneRatio A hA g
      let f := referencePlaneCubicObjective A hA (ε • g) (scaleBinaryCubic B t)
      let hpos : 0<referenceAtomCount A hA (ε • g) := by rw [referenceAtomCount_scalar A hA g ε hε.ne']; omega
      let M := budgetedCentreEndpointMethod (metricCoordinates A hA) B hpos f 0
      ‖(metricCoordinates A hA).symm (gradient f
        (scalarFunctionPoint M (metricCoordinates A hA) f (gradient f) R 0 (referenceAtomCount A hA (ε • g))))‖≤
        B^2*(r^2/4*Real.sqrt (1+4*r^2)*fibreMinimax r)*p^3+C*p^4 := by
  obtain ⟨R,ep,hR,hep,hdom⟩ := referencePlane_small_source_domain A hA g hN B hB
  obtain ⟨C,hC,hupper⟩ := budgetedPlaneCentreOutput_gradient_upper B (referencePlaneRatio A hA g) hB
  let p₀ := ‖canonicalCGStep A g 0‖
  have hp₀ : 0<p₀ := (referencePlane_sample_lines A hA g hN).1
  have hd : 0<B*p₀+1 := add_pos (mul_pos hB hp₀) zero_lt_one
  refine ⟨R,min ep (1/(B*p₀+1)),C,hR,lt_min hep (div_pos zero_lt_one hd),hC,?_⟩
  intro ε hε heps t ht
  dsimp only
  have hNε : 2≤referenceAtomCount A hA (ε • g) := by rwa [referenceAtomCount_scalar A hA g ε hε.ne']
  have hp : 0<ε*p₀ := mul_pos hε hp₀
  have hps : B*(ε*p₀)≤1 := by
    have hh := (lt_div_iff₀ hd).mp (heps.trans_le (min_le_right _ _))
    nlinarith only [hh,hε]
  have hD := hdom ε hε (heps.trans_le (min_le_left _ _)) B hB.le le_rfl t ht
  rw [referencePlaneCubic_endpoint_global_eq_output A hA (ε • g) hNε (scaleBinaryCubic B t) R hD.1 hD.2 B,
    OneCorrectionValueMethod.output_reference A hA (ε • g) hNε (scaleBinaryCubic B t) R hD.1 hD.2]
  change ‖(metricCoordinates A hA).symm (gradient (referencePlaneCubicObjective A hA (ε • g) (scaleBinaryCubic B t))
    (metricPlaneResponseFinalPolicy (budgetedPlaneCentreOutput B) (metricCoordinates A hA) (by omega)
      (methodRun (fcMethod fullMemory) (fun _=>cgOperator A) (fun _=>cgOperator A) (ε • g) (referenceAtomCount A hA (ε • g)-1))
      (functionSearchTranscript (referencePlaneCubicObjective A hA (ε • g) (scaleBinaryCubic B t))
        (CG.displacement (cgOperator A) (ε • g)) (referenceStep (cgOperator A) (ε • g)) (referenceAtomCount A hA (ε • g)))))‖≤_
  apply (referencePlaneCubic_response_gradient_le (budgetedPlaneCentreOutput B) A hA (ε • g) hNε (scaleBinaryCubic B t) _).trans
  rw [referencePlaneFirstLength_scalar A hA g hε,referencePlaneRatio_scalar A hA g hε]
  exact hupper (ε*p₀) hp hps t ht

end
end krylov.Functions
