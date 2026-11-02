import krylov.Functions.ReferencePlaneRFCFObservations
import krylov.Functions.ReferencePlaneRFCFGeometry
import krylov.Functions.MetricValueModelOutput

/-!
Article: main_krylov, thm:Fplanar, literal full-n native RFC-F output.
Use: reduce the actual original scalar RFC-F executor to the genuine planar
value-model output, through its real full CG step window and SPD-root map.
Source: actual native prefix replay, complete observed model reduction,
true Galerkin solve uniqueness and actual metric value-model covariance.
-/
namespace krylov.Functions
noncomputable section
open Matrix Finset krylov.Reference krylov.Tensor krylov.Nonlinear krylov.Methods krylov.Correction
open scoped InnerProductSpace BigOperators Matrix.Norms.L2Operator
variable {n k : ℕ}

/-- A genuinely accepted native RFC-F model returns the literal observed
value-model output of its real retained pairs and last searched endpoint.
Article: main_krylov, thm:Fplanar, actual executor pointer dictionary. -/
theorem rfcFPoint_eq_observedValueModelOutput
    (T : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (R : ℝ) (x : EuclideanSpace ℝ (Fin n)) (k : ℕ)
    (hgate : rfcFunctionGate fullMemory (rfcFunctionRun T f (gradient f) fullMemory R x k)) :
    rfcFPoint T f (gradient f) R x k=
      observedValueModelOutput f (rfcFAnchors T f (gradient f) R x k)
        (rfcFSteps T f (gradient f) R x k) (rfcFAnchor T f (gradient f) R x k) := by
  simp only [rfcFPoint,rfcFCorrectionStep,ite_eq_left hgate]
  rfl

set_option maxHeartbeats 1200000 in
/-- The literal original full-n RFC-F returned point equals the embedded
actual planar corrected-model output. The prefix, all actual model-metric
splits, every middle pair and the accepted gate are proved from the scalar
source and genuine active CG reference.
Article: main_krylov, thm:Fplanar, complete native full-cycle dictionary. -/
theorem referencePlaneCubic_rfcFPoint_eq_plane
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) (g : EuclideanSpace ℝ (Fin n))
    (hc : referenceAtomCount A hA g=k+2)
    (t : krylov.Tensor.BinaryCubic) (R : ℝ) (hH : ReferencePlanePositiveBall A hA g t R)
    (hnodes : ∀ i≤referenceAtomCount A hA g, ‖referencePlaneNode A g i‖≤R)
    (hsmall : ‖canonicalCGStep A g 0‖*‖planeRFCFModelOperator (referencePlaneRatio A hA g) t‖≤1/2) :
    metricCoordinates A hA
      (rfcFPoint (metricCoordinates A hA) (referencePlaneCubicObjective A hA g t)
        (gradient (referencePlaneCubicObjective A hA g t)) R 0 (k+1))=
    hilbertPlaneEmbed (referencePlaneFirst A g) (referencePlaneLast A hA g)
      (planeRFCFOutput ‖canonicalCGStep A g 0‖ (referencePlaneRatio A hA g) t)+
        referencePlaneComplement A hA g := by
  let S := metricCoordinates A hA
  let e := referencePlaneFirst A g
  let h := referencePlaneLast A hA g
  let m := referencePlaneComplement A hA g
  let p := ‖canonicalCGStep A g 0‖
  let r := referencePlaneRatio A hA g
  let f := referencePlaneCubicObjective A hA g t
  let fcan := hilbertPlaneObjective e h m p r t
  let a := fun i : Fin (k+2)=>CG.displacement (cgOperator A) g i.val
  let s := fun i : Fin (k+2)=>referenceStep (cgOperator A) g i.val
  let z := CG.displacement (cgOperator A) g (k+2)
  obtain ⟨ha,hs,hz,hgate⟩ := referencePlaneCubic_rfcF_observations A hA g hc t R hH hnodes
  have hae : rfcFAnchors S f (gradient f) R 0 (k+1)=a := funext ha
  have hse : rfcFSteps S f (gradient f) R 0 (k+1)=s := funext hs
  rw [rfcFPoint_eq_observedValueModelOutput _ _ _ _ _ hgate,hae,hse,hz]
  have hS := referencePlane_metric_symmetric A hA
  have hdf z : DifferentiableAt ℝ fcan z := (hilbertPlaneObjective_hasFDerivAt e h m p r t z).differentiableAt
  have hmetric := observedValueModelOutput_metric S hS fcan hdf a s z
  change S (observedValueModelOutput f a s z)=_ at hmetric
  rw [hmetric]
  have haS : (fun i=>S (a i))=(fun i : Fin (k+2)=>referencePlaneNode A g i.val) := by
    funext i
    exact (referencePlaneNode_metric A hA g i.val).symm
  have hsS : (fun i=>S (s i))=(fun i : Fin (k+2)=>canonicalCGStep A g i.val) := by
    funext i
    dsimp only [S,s,referenceStep]
    simp only [canonicalCGStep,cgStep,map_smul,metricCoordinates_apply]
    rfl
  have hzS : S z=hilbertPlaneTerminal e h m p r := by
    rw [←referencePlaneNode_metric]
    have ht := referencePlaneTerminal_eq_node A hA g
    simpa only [hc] using ht.symm
  rw [haS,hsS,hzS]
  have hN : 2≤referenceAtomCount A hA g := by omega
  obtain ⟨hp,hr,he,hh,heh,_,_⟩ := referencePlane_sample_lines A hA g hN
  obtain ⟨hpa,hps,hfirst,hlast,hind,hfuture,hend⟩ := referencePlaneRFCF_window_geometry A hA g hc
  exact hilbertPlaneRFCFOutput_eq_plane (by intro hh; have hv := congrArg Fin.val hh; change 0=k+2-1 at hv; omega)
    e h m he hh heh (referencePlaneComplement_project A hA g hN) p r hp hr.ne' t _ _
    hpa hps hfirst hlast hind hfuture hend hsmall

set_option maxHeartbeats 1000000 in
/-- The normalized true gradient of the literal original full-n native
RFC-F output has exactly the actual planar output-gradient norm.
Article: main_krylov, thm:Fplanar, full native C_Y transfer. -/
theorem referencePlaneCubic_rfcFPoint_gradient_norm
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) (g : EuclideanSpace ℝ (Fin n))
    (hc : referenceAtomCount A hA g=k+2)
    (t : krylov.Tensor.BinaryCubic) (R : ℝ) (hH : ReferencePlanePositiveBall A hA g t R)
    (hnodes : ∀ i≤referenceAtomCount A hA g, ‖referencePlaneNode A g i‖≤R)
    (hsmall : ‖canonicalCGStep A g 0‖*‖planeRFCFModelOperator (referencePlaneRatio A hA g) t‖≤1/2) :
    ‖(metricCoordinates A hA).symm
      (gradient (referencePlaneCubicObjective A hA g t)
        (rfcFPoint (metricCoordinates A hA) (referencePlaneCubicObjective A hA g t)
          (gradient (referencePlaneCubicObjective A hA g t)) R 0 (k+1)))‖=
    ‖gradient (planeCubicObjective ‖canonicalCGStep A g 0‖ (referencePlaneRatio A hA g) t)
      (planeRFCFOutput ‖canonicalCGStep A g 0‖ (referencePlaneRatio A hA g) t)‖ := by
  have hpnt := referencePlaneCubic_rfcFPoint_eq_plane A hA g hc t R hH hnodes hsmall
  have hN : 2≤referenceAtomCount A hA g := by omega
  obtain ⟨_,_,he,hh,heh,_,_⟩ := referencePlane_sample_lines A hA g hN
  conv_lhs =>
    arg 1
    rw [show gradient (referencePlaneCubicObjective A hA g t)=
      gradient (metricHilbertPlaneObjective (metricCoordinates A hA) (referencePlaneFirst A g)
        (referencePlaneLast A hA g) (referencePlaneComplement A hA g)
        ‖canonicalCGStep A g 0‖ (referencePlaneRatio A hA g) t) from rfl]
  rw [metricHilbertPlaneGradient_normalized _ (referencePlane_metric_symmetric A hA)]
  change ‖gradient (hilbertPlaneObjective (referencePlaneFirst A g) (referencePlaneLast A hA g)
    (referencePlaneComplement A hA g) ‖canonicalCGStep A g 0‖ (referencePlaneRatio A hA g) t)
    (metricCoordinates A hA (rfcFPoint (metricCoordinates A hA) (referencePlaneCubicObjective A hA g t)
      (gradient (referencePlaneCubicObjective A hA g t)) R 0 (k+1)))‖=_
  rw [hpnt]
  have hg := hilbertPlaneRFCF_corrected_gradient (referencePlaneFirst A g) (referencePlaneLast A hA g)
    (referencePlaneComplement A hA g) he hh heh (referencePlaneComplement_project A hA g hN)
    ‖canonicalCGStep A g 0‖ (referencePlaneRatio A hA g) t
    (planeRFCFCorrection ‖canonicalCGStep A g 0‖ (referencePlaneRatio A hA g) t)
  have hgn := congrArg norm hg
  rw [hilbertPlaneEmbed_norm (referencePlaneFirst A g) (referencePlaneLast A hA g) he hh heh] at hgn
  simpa only [hilbertPlaneTerminal,planeRFCFOutput,map_add,add_assoc,add_left_comm,add_comm] using hgn

end
end krylov.Functions
