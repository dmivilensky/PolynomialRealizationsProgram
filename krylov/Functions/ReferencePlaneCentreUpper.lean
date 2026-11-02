import krylov.Functions.MetricPlaneResponsePolicy

/-!
Article: main_krylov, thm:Fplanar, attaining original scalar-function policy.
Use: realize the data-only fibre centre as one actual retained-span final
correction after a genuine CG-consistent scalar prefix. Source: the actual
endpoint observer, true quadratic-zero guard and full-plane gradient lift.
-/
namespace krylov.Functions
noncomputable section
open Finset krylov.Methods krylov.Reference krylov.Tensor krylov.Nonlinear krylov.Tensor.BinaryCubic
open scoped InnerProductSpace BigOperators Matrix.Norms.L2Operator
variable {n : ℕ}

set_option maxHeartbeats 800000 in
/-- When the observed residual is nonzero, the genuine data-only centre
policy equals the exact full-space lift of the planar centre output.
Article: main_krylov, thm:Fplanar. -/
theorem referencePlaneCubic_centre_output (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hN : 2≤referenceAtomCount A hA g) (t : krylov.Tensor.BinaryCubic)
    (H : History (EuclideanSpace ℝ (Fin n)))
    (hnz : inner ℝ (gradient (referencePlaneCubicObjective A hA g t)
      (CG.displacement (cgOperator A) g (referenceAtomCount A hA g))) (referenceStep (cgOperator A) g 0)≠0) :
    metricPlaneCentreFinalPolicy (metricCoordinates A hA) (by omega) H
      (functionSearchTranscript (referencePlaneCubicObjective A hA g t)
        (CG.displacement (cgOperator A) g) (referenceStep (cgOperator A) g) (referenceAtomCount A hA g))=
    (metricCoordinates A hA).symm
      (hilbertPlaneEmbed (referencePlaneFirst A g) (referencePlaneLast A hA g)
        (planeCentreOutput (referencePlaneRatio A hA g) ‖canonicalCGStep A g 0‖
          (observe (referencePlaneRatio A hA g) t))+referencePlaneComplement A hA g) := by
  exact referencePlaneCubic_response_output planeCentreOutput A hA g hN t H hnz

set_option maxHeartbeats 800000 in
/-- The actual observed zero guard means the full true terminal gradient
is zero on the genuine scalar source. No correction is then necessary.
Article: main_krylov, thm:Fplanar. -/
theorem referencePlaneCubic_terminal_gradient_zero (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hN : 2≤referenceAtomCount A hA g) (t : krylov.Tensor.BinaryCubic)
    (hz : inner ℝ (gradient (referencePlaneCubicObjective A hA g t)
      (CG.displacement (cgOperator A) g (referenceAtomCount A hA g))) (referenceStep (cgOperator A) g 0)=0) :
    gradient (referencePlaneCubicObjective A hA g t)
      (CG.displacement (cgOperator A) g (referenceAtomCount A hA g))=0 := by
  let S := metricCoordinates A hA
  let e := referencePlaneFirst A g
  let p := ‖canonicalCGStep A g 0‖
  let r := referencePlaneRatio A hA g
  let G := gradient (referencePlaneCubicObjective A hA g t)
  let x := CG.displacement (cgOperator A) g (referenceAtomCount A hA g)
  let c := p^2*r/2*(t.t1+r*t.t2)
  obtain ⟨hp,_,he,_,_,_,_⟩ := referencePlane_sample_lines A hA g hN
  change 0<p at hp
  change ‖e‖=1 at he
  have hg : S.symm (G x)=c • e := referencePlaneCubic_terminal_gradient A hA g hN t
  have hs : S (referenceStep (cgOperator A) g 0)=p • e := by
    rw [referencePlaneStep_metric]
    exact (NormedSpace.norm_smul_normalize _).symm
  have hpairs := metricHilbertPlaneGradient_pair S (referencePlane_metric_symmetric A hA)
    (referencePlaneFirst A g) (referencePlaneLast A hA g) (referencePlaneComplement A hA g)
    p r t x (referenceStep (cgOperator A) g 0)
  rw [←metricHilbertPlaneGradient_normalized S (referencePlane_metric_symmetric A hA)] at hpairs
  change inner ℝ (G x) (referenceStep (cgOperator A) g 0)=inner ℝ (S.symm (G x)) (S (referenceStep (cgOperator A) g 0)) at hpairs
  rw [hg,hs,real_inner_smul_left,real_inner_smul_right,real_inner_self_eq_norm_sq,he] at hpairs
  have hc : c=0 := (mul_eq_zero.mp (show c*p=0 by simpa only [one_pow,mul_one] using hpairs.symm.trans hz)).resolve_right hp.ne'
  apply S.symm.injective
  rw [hg,hc,zero_smul,map_zero]

set_option maxHeartbeats 800000 in
/-- Any endpoint-data response has its true full-space gradient bounded by
its actual planar gradient. The observed zero guard gives the stationary
branch; otherwise the full-space lift is exact. Article: thm:Fplanar. -/
theorem referencePlaneCubic_response_gradient_le (response : ℝ → ℝ → Observation → Plane)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hN : 2≤referenceAtomCount A hA g) (t : krylov.Tensor.BinaryCubic)
    (H : History (EuclideanSpace ℝ (Fin n))) :
    let p := ‖canonicalCGStep A g 0‖
    let r := referencePlaneRatio A hA g
    let f := referencePlaneCubicObjective A hA g t
    let data := functionSearchTranscript f (CG.displacement (cgOperator A) g)
      (referenceStep (cgOperator A) g) (referenceAtomCount A hA g)
    ‖(metricCoordinates A hA).symm (gradient f
      (metricPlaneResponseFinalPolicy response (metricCoordinates A hA) (by omega) H data))‖≤
      ‖gradient (planeCubicObjective p r t) (response r p (observe r t))‖ := by
  classical
  dsimp only
  obtain ⟨_,_,he,hh,heh,_,_⟩ := referencePlane_sample_lines A hA g hN
  change ‖referencePlaneFirst A g‖=1 at he
  change ‖referencePlaneLast A hA g‖=1 at hh
  change inner ℝ (referencePlaneFirst A g) (referencePlaneLast A hA g)=0 at heh
  by_cases hz : inner ℝ (gradient (referencePlaneCubicObjective A hA g t)
    (CG.displacement (cgOperator A) g (referenceAtomCount A hA g))) (referenceStep (cgOperator A) g 0)=0
  · rw [metricPlaneResponseFinalPolicy,observedSpanFinalPolicy_guard_zero _ _ _ _ hz]
    change ‖(metricCoordinates A hA).symm (gradient (referencePlaneCubicObjective A hA g t)
      (CG.displacement (cgOperator A) g (referenceAtomCount A hA g)))‖≤_
    rw [referencePlaneCubic_terminal_gradient_zero A hA g hN t hz,map_zero,norm_zero]
    exact norm_nonneg _
  · rw [referencePlaneCubic_response_output response A hA g hN t H hz,referencePlaneCubicObjective,
      metricHilbertPlaneGradient_lifted_norm _ (referencePlane_metric_symmetric A hA) _ _ _ he hh heh
        (referencePlaneComplement_project A hA g hN)]

set_option maxHeartbeats 800000 in
/-- The endpoint-only original retained-span centre policy attains the
sharp full-space gradient upper coefficient uniformly over the genuine
binary tensor ball, including its exact stationary branch.
Article: main_krylov, thm:Fplanar. -/
theorem referencePlaneCubic_centre_gradient_upper (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hN : 2≤referenceAtomCount A hA g) :
    ∃ C : ℝ, 0<C ∧ ∀ t : krylov.Tensor.BinaryCubic, t.InBall →
      ∀ H : History (EuclideanSpace ℝ (Fin n)),
      let p := ‖canonicalCGStep A g 0‖
      let r := referencePlaneRatio A hA g
      let f := referencePlaneCubicObjective A hA g t
      let data := functionSearchTranscript f (CG.displacement (cgOperator A) g)
        (referenceStep (cgOperator A) g) (referenceAtomCount A hA g)
      p≤1 → ‖(metricCoordinates A hA).symm (gradient f
        (metricPlaneCentreFinalPolicy (metricCoordinates A hA) (by omega) H data))‖≤
        r^2/4*Real.sqrt (1+4*r^2)*fibreMinimax r*p^3+C*p^4 := by
  obtain ⟨C,hC,hupper⟩ := planeCentreOutput_gradient_upper (referencePlaneRatio A hA g)
  refine ⟨C,hC,?_⟩
  intro t ht H
  dsimp only
  intro hp₁
  obtain ⟨hp,_,_,_,_,_,_⟩ := referencePlane_sample_lines A hA g hN
  exact (referencePlaneCubic_response_gradient_le planeCentreOutput A hA g hN t H).trans
    (hupper _ hp hp₁ t ht)

end
end krylov.Functions
