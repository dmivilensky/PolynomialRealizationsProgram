import krylov.Functions.ReferencePlaneObservedData

/-!
Article: main_krylov, thm:Fplanar, general observed plane response.
Use: realize any endpoint-data response by an original retained-span final
correction with genuine global quadratic-zero behaviour. Source: actual
endpoint observation recovery and the proved exact full-reference geometry.
-/
namespace krylov.Functions
noncomputable section
open Finset krylov.Methods krylov.Reference krylov.Tensor krylov.Nonlinear krylov.Tensor.BinaryCubic
open scoped InnerProductSpace BigOperators Matrix.Norms.L2Operator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Explicit data-only first/last-step coefficients of an arbitrary
observed plane response. Article: main_krylov, thm:Fplanar. -/
def metricPlaneResponseCoefficients (response : ℝ → ℝ → Observation → Plane) {N : ℕ} (S : E ≃L[ℝ] E) (hN : 0<N)
    (_H : History E) (data : FunctionSearchTranscript E N) (i : Fin N) : ℝ :=
  let p := ‖S (data.lineSteps ⟨0,hN⟩)‖
  let v := ‖S (data.lineSteps ⟨N-1,by omega⟩)‖
  let z := response (v/p) p (metricPlaneCentreData S hN data)
  (if i=⟨0,hN⟩ then (z 0-p)/p else 0)+
    (if i=⟨N-1,by omega⟩ then (z 1-v)/v else 0)

/-- A genuine original retained-span one-correction final policy.
All information is actual endpoint data, and global quadratic-zero
behaviour follows from ScalarValueFinalRules for these coefficients.
Article: main_krylov, thm:Fplanar. -/
def metricPlaneResponseFinalPolicy (response : ℝ → ℝ → Observation → Plane) {N : ℕ} (S : E ≃L[ℝ] E) (hN : 0<N) :
    History E → FunctionSearchTranscript E N → E :=
  observedSpanFinalPolicy hN (metricPlaneResponseCoefficients response S hN)

omit [CompleteSpace E] in
/-- The response displacement is literally a combination of the first and
last retained physical steps. Article: main_krylov, thm:Fplanar. -/
theorem metricPlaneResponse_sum (response : ℝ → ℝ → Observation → Plane) {N : ℕ} (S : E ≃L[ℝ] E) (hN : 0<N)
    (H : History E) (data : FunctionSearchTranscript E N) :
    ∑ i,metricPlaneResponseCoefficients response S hN H data i • data.lineSteps i=
      let p := ‖S (data.lineSteps ⟨0,hN⟩)‖
      let v := ‖S (data.lineSteps ⟨N-1,by omega⟩)‖
      let z := response (v/p) p (metricPlaneCentreData S hN data)
      ((z 0-p)/p) • data.lineSteps ⟨0,hN⟩+((z 1-v)/v) • data.lineSteps ⟨N-1,by omega⟩ := by
  classical
  simp only [metricPlaneResponseCoefficients,add_smul,sum_add_distrib,ite_smul,zero_smul]
  simp

variable {n : ℕ}

set_option maxHeartbeats 800000 in
/-- When the observed residual is nonzero, the genuine data-only response
policy equals the exact full-space lift of its prescribed plane output.
Article: main_krylov, thm:Fplanar. -/
theorem referencePlaneCubic_response_output (response : ℝ → ℝ → Observation → Plane)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hN : 2≤referenceAtomCount A hA g) (t : krylov.Tensor.BinaryCubic)
    (H : History (EuclideanSpace ℝ (Fin n)))
    (hnz : inner ℝ (gradient (referencePlaneCubicObjective A hA g t)
      (CG.displacement (cgOperator A) g (referenceAtomCount A hA g))) (referenceStep (cgOperator A) g 0)≠0) :
    metricPlaneResponseFinalPolicy response (metricCoordinates A hA) (by omega) H
      (functionSearchTranscript (referencePlaneCubicObjective A hA g t)
        (CG.displacement (cgOperator A) g) (referenceStep (cgOperator A) g) (referenceAtomCount A hA g))=
    (metricCoordinates A hA).symm
      (hilbertPlaneEmbed (referencePlaneFirst A g) (referencePlaneLast A hA g)
        (response (referencePlaneRatio A hA g) ‖canonicalCGStep A g 0‖
          (observe (referencePlaneRatio A hA g) t))+referencePlaneComplement A hA g) := by
  classical
  let N := referenceAtomCount A hA g
  let p := ‖canonicalCGStep A g 0‖
  let v := ‖canonicalCGStep A g (N-1)‖
  let r := referencePlaneRatio A hA g
  let e := referencePlaneFirst A g
  let h := referencePlaneLast A hA g
  let m := referencePlaneComplement A hA g
  let S := metricCoordinates A hA
  let f := referencePlaneCubicObjective A hA g t
  let data := functionSearchTranscript f (CG.displacement (cgOperator A) g) (referenceStep (cgOperator A) g) N
  let z := response r p (observe r t)
  obtain ⟨hp,hr,_,_,_,_,_⟩ := referencePlane_sample_lines A hA g hN
  change 0<p at hp
  change 0<r at hr
  have hpr : r*p=v := div_mul_cancel₀ _ hp.ne'
  have hv : v≠0 := by rw [←hpr]; exact (mul_pos hr hp).ne'
  have hs0 : S (referenceStep (cgOperator A) g 0)=p • e := by
    rw [referencePlaneStep_metric]
    exact (NormedSpace.norm_smul_normalize _).symm
  have hsl : S (referenceStep (cgOperator A) g (N-1))=v • h := by
    rw [referencePlaneStep_metric]
    exact (NormedSpace.norm_smul_normalize _).symm
  unfold metricPlaneResponseFinalPolicy observedSpanFinalPolicy observedSpanFinalCorrection
  change observedFinalPoint data+(if inner ℝ (gradient f (CG.displacement (cgOperator A) g N))
    (referenceStep (cgOperator A) g 0)=0 then 0 else ∑ i,metricPlaneResponseCoefficients response S (by omega) H data i • data.lineSteps i)=_
  rw [ite_eq_right hnz,metricPlaneResponse_sum response,referencePlaneCubic_observed_data A hA g hN t]
  change CG.displacement (cgOperator A) g N+
    (((z 0-p)/p) • referenceStep (cgOperator A) g 0+
      ((z 1-v)/v) • referenceStep (cgOperator A) g (N-1))=S.symm (hilbertPlaneEmbed e h z+m)
  apply S.injective
  simp only [map_add,map_smul,S.apply_symm_apply,hs0,hsl]
  rw [←referencePlaneNode_metric,←referencePlaneTerminal_eq_node]
  change (hilbertPlaneEmbed e h (planeOfPair (p,r*p))+m)+
    (((z 0-p)/p) • (p • e)+((z 1-v)/v) • (v • h))=hilbertPlaneEmbed e h z+m
  rw [smul_smul,smul_smul,div_mul_cancel₀ _ hp.ne',div_mul_cancel₀ _ hv,
    hilbertPlaneEmbed_apply,hilbertPlaneEmbed_apply]
  simp only [planeOfPair,Matrix.cons_val_zero,Matrix.cons_val_one]
  rw [←hpr]
  module


end
end krylov.Functions
