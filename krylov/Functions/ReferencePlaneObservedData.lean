import krylov.Functions.MetricPlaneObservedCentre

/-!
Article: main_krylov, thm:Fplanar, actual observed reference dictionary.
Use: extract the original three observed coefficients from the genuinely
executed first and last scalar segments of a full reference cycle.
Source: true CG frame coordinates and actual quadratic-defect cancellation.
-/
namespace krylov.Functions
noncomputable section
open Finset krylov.Methods krylov.Reference krylov.Tensor krylov.Nonlinear krylov.Tensor.BinaryCubic
open scoped InnerProductSpace BigOperators Matrix.Norms.L2Operator
variable {n : ℕ}

/-- The exact projected initial, first, penultimate and last reference
nodes. Every coordinate follows from the actual orthogonal CG frame.
Article: main_krylov, thm:Fplanar. -/
theorem referencePlane_project_samples (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hN : 2≤referenceAtomCount A hA g) :
    let N := referenceAtomCount A hA g
    let P := hilbertPlaneProject (referencePlaneFirst A g) (referencePlaneLast A hA g)
    let p := ‖canonicalCGStep A g 0‖
    let r := referencePlaneRatio A hA g
    P (referencePlaneNode A g 0)=0 ∧
    P (referencePlaneNode A g 1)=planeOfPair (p,0) ∧
    P (referencePlaneNode A g (N-1))=planeOfPair (p,0) ∧
    P (referencePlaneNode A g N)=planeOfPair (p,r*p) := by
  let N := referenceAtomCount A hA g
  let p := ‖canonicalCGStep A g 0‖
  let r := referencePlaneRatio A hA g
  obtain ⟨hp,_,_,_,_,_,_⟩ := referencePlane_sample_lines A hA g hN
  have hpr : r*p=‖canonicalCGStep A g (N-1)‖ := div_mul_cancel₀ _ hp.ne'
  let i0 : Fin N := ⟨0,by omega⟩
  let il : Fin N := ⟨N-1,by omega⟩
  have hc k (hk : k≤N) :
      hilbertPlaneProject (referencePlaneFirst A g) (referencePlaneLast A hA g) (referencePlaneNode A g k)=
      planeOfPair (if 0<k then p else 0,if N-1<k then r*p else 0) := by
    have h0 := referencePlaneNode_unit_coordinate A hA g i0 k hk
    have hl := referencePlaneNode_unit_coordinate A hA g il k hk
    change inner ℝ (referencePlaneFirst A g) (referencePlaneNode A g k)=(if 0<k then p else 0) at h0
    change inner ℝ (referencePlaneLast A hA g) (referencePlaneNode A g k)=(if N-1<k then ‖canonicalCGStep A g (N-1)‖ else 0) at hl
    rw [hilbertPlaneProject_apply,h0,hl,hpr]
  have hz : planeOfPair (0,0)=0 := by ext i; fin_cases i <;> rfl
  refine ⟨?_,?_,?_,?_⟩
  · simpa only [Nat.lt_irrefl,show ¬(N-1<0) by omega,ite_false,hz] using hc 0 (by omega)
  · simpa only [show 0<1 by omega,show ¬(N-1<1) by omega,ite_true,ite_false] using hc 1 (by omega)
  · simpa only [show 0<N-1 by omega,Nat.lt_irrefl,ite_true,ite_false] using hc (N-1) (by omega)
  · simpa only [show 0<N by omega,show N-1<N by omega,ite_true] using hc N le_rfl

/-- The exact first and last reference step projections, with the original
physical reference scaling. Article: main_krylov, thm:Fplanar. -/
theorem referencePlane_project_steps (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hN : 2≤referenceAtomCount A hA g) :
    let N := referenceAtomCount A hA g
    let P := hilbertPlaneProject (referencePlaneFirst A g) (referencePlaneLast A hA g)
    let p := ‖canonicalCGStep A g 0‖
    let r := referencePlaneRatio A hA g
    P (canonicalCGStep A g 0)=planeOfPair (p,0) ∧
      P (canonicalCGStep A g (N-1))=planeOfPair (0,r*p) := by
  obtain ⟨h0,h1,hl,hN'⟩ := referencePlane_project_samples A hA g hN
  have hs i : referencePlaneNode A g (i+1)=referencePlaneNode A g i+canonicalCGStep A g i :=
    sum_range_succ _ i
  constructor
  · have hh := congrArg (hilbertPlaneProject (referencePlaneFirst A g) (referencePlaneLast A hA g)) (hs 0)
    rw [map_add,h0,h1,zero_add] at hh
    exact hh.symm
  · have hh := congrArg (hilbertPlaneProject (referencePlaneFirst A g) (referencePlaneLast A hA g))
      (hs (referenceAtomCount A hA g-1))
    rw [show referenceAtomCount A hA g-1+1=referenceAtomCount A hA g by omega,map_add,hN',hl] at hh
    apply add_left_cancel (a:=planeOfPair (‖canonicalCGStep A g 0‖,0))
    rw [←hh,←planeOfPair_add]
    congr 1
    ext <;> simp

/-- The normalized actual full terminal gradient is precisely the observed
binary scalar in the true first reference direction.
Article: main_krylov, thm:Fplanar. -/
theorem referencePlaneCubic_terminal_gradient (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hN : 2≤referenceAtomCount A hA g) (t : krylov.Tensor.BinaryCubic) :
    (metricCoordinates A hA).symm (gradient (referencePlaneCubicObjective A hA g t)
      (CG.displacement (cgOperator A) g (referenceAtomCount A hA g)))=
      (‖canonicalCGStep A g 0‖^2*referencePlaneRatio A hA g/2*(t.t1+referencePlaneRatio A hA g*t.t2)) •
        referencePlaneFirst A g := by
  obtain ⟨_,_,he,hh,heh,_,_⟩ := referencePlane_sample_lines A hA g hN
  change ‖referencePlaneFirst A g‖=1 at he
  change ‖referencePlaneLast A hA g‖=1 at hh
  change inner ℝ (referencePlaneFirst A g) (referencePlaneLast A hA g)=0 at heh
  rw [referencePlaneCubicObjective,metricHilbertPlaneGradient_normalized _ (referencePlane_metric_symmetric A hA),
    ←referencePlaneNode_metric,←referencePlaneTerminal_eq_node]
  exact hilbertPlaneGradient_terminal _ _ _ he hh heh (referencePlaneComplement_project A hA g hN) _ _ t

set_option maxHeartbeats 800000 in
/-- The implementable full-dimensional observer recovers precisely the
three original observable coefficients from real endpoint data.
The hidden coefficient and unknown tensor never enter the observer.
Article: main_krylov, thm:Fplanar, attaining policy dictionary. -/
theorem referencePlaneCubic_observed_data (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hN : 2≤referenceAtomCount A hA g) (t : krylov.Tensor.BinaryCubic) :
    metricPlaneCentreData (metricCoordinates A hA) (by omega)
      (functionSearchTranscript (referencePlaneCubicObjective A hA g t)
        (CG.displacement (cgOperator A) g) (referenceStep (cgOperator A) g) (referenceAtomCount A hA g))=
      observe (referencePlaneRatio A hA g) t := by
  let N := referenceAtomCount A hA g
  let p := ‖canonicalCGStep A g 0‖
  let r := referencePlaneRatio A hA g
  let e := referencePlaneFirst A g
  let h := referencePlaneLast A hA g
  let m := referencePlaneComplement A hA g
  let S := metricCoordinates A hA
  let f := referencePlaneCubicObjective A hA g t
  let data := functionSearchTranscript f (CG.displacement (cgOperator A) g) (referenceStep (cgOperator A) g) N
  let i0 : Fin N := ⟨0,by omega⟩
  let il : Fin N := ⟨N-1,by omega⟩
  obtain ⟨hp,hr,he,_,_,_,_⟩ := referencePlane_sample_lines A hA g hN
  change 0<p at hp
  change 0<r at hr
  change ‖e‖=1 at he
  obtain ⟨hP0,_,hPl,_⟩ := referencePlane_project_samples A hA g hN
  obtain ⟨hS0,hSl⟩ := referencePlane_project_steps A hA g hN
  have hd0 : observedPairDefect data i0=
      segmentValueDefect (planeCubicObjective p r t) (fun x=>innerSL ℝ (gradient (planeCubicObjective p r t) x))
        0 (planeOfPair (p,0)) := by
    rw [observedPairDefect_reference]
    change segmentValueDefect (metricHilbertPlaneObjective S e h m p r t)
      (fun x=>innerSL ℝ (gradient (metricHilbertPlaneObjective S e h m p r t) x))
      (CG.displacement (cgOperator A) g 0) (referenceStep (cgOperator A) g 0)=_
    rw [metricHilbertPlane_value_defect S (referencePlane_metric_symmetric A hA),
      ←referencePlaneNode_metric,referencePlaneStep_metric,hP0,hS0]
  have hdl : observedPairDefect data il=
      segmentValueDefect (planeCubicObjective p r t) (fun x=>innerSL ℝ (gradient (planeCubicObjective p r t) x))
        (planeOfPair (p,0)) (planeOfPair (0,r*p)) := by
    rw [observedPairDefect_reference]
    change segmentValueDefect (metricHilbertPlaneObjective S e h m p r t)
      (fun x=>innerSL ℝ (gradient (metricHilbertPlaneObjective S e h m p r t) x))
      (CG.displacement (cgOperator A) g (N-1)) (referenceStep (cgOperator A) g (N-1))=_
    rw [metricHilbertPlane_value_defect S (referencePlane_metric_symmetric A hA),
      ←referencePlaneNode_metric,referencePlaneStep_metric,hPl,hSl]
  have hg : S.symm (observedFinalGradient data)=(p^2*r/2*(t.t1+r*t.t2)) • e :=
    referencePlaneCubic_terminal_gradient A hA g hN t
  change metricPlaneObservedBinaryData S e p r (observedPairDefect data i0) (observedPairDefect data il)
    (observedFinalGradient data)=observe r t
  unfold metricPlaneObservedBinaryData observe
  rw [hd0,hdl,hg,real_inner_smul_right,real_inner_self_eq_norm_sq,he]
  obtain ⟨hfirst,hlast⟩ := plane_observed_pure_coefficients p r hp.ne' hr.ne' t
  rw [hfirst,hlast]
  congr 1
  field_simp [hp.ne',hr.ne']

end
end krylov.Functions
