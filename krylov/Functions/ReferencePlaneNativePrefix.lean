import krylov.Functions.ReferencePlaneStationarity
import krylov.Functions.HilbertPlaneExactSearch
import krylov.Functions.HilbertPlaneHessianBounds

/-!
Article: main_krylov, prop:Fcycle(iii), actual class-M scalar prefix.
Use: derive the genuine scalar execution from global CG consistency and the
original positive cubic search domain. Every true intermediate correction
is zero; the actual final line reaches the common last reference point.
Source: actual scalar causal replay and the proved actual source stationarity.
-/
namespace krylov.Functions
noncomputable section
open Matrix Finset krylov.Reference krylov.Tensor krylov.Nonlinear krylov.Methods
open scoped InnerProductSpace BigOperators Matrix.Norms.L2Operator
variable {n : ℕ}

/-- Positivity of the actual full scalar source Hessian on its original
canonical search ball. This is a derivative condition, not a trajectory
condition; a uniform such ball is derived in HilbertPlaneHessianBounds.
Article: main_krylov, prop:Fcycle(iii). -/
def ReferencePlanePositiveBall (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (t : krylov.Tensor.BinaryCubic) (R : ℝ) : Prop :=
  ∀ z : EuclideanSpace ℝ (Fin n), ‖z‖≤R → ∀ v : EuclideanSpace ℝ (Fin n),
    ‖v‖^2/2 ≤ inner ℝ v
      (hilbertPlaneHessian (referencePlaneFirst A g) (referencePlaneLast A hA g)
        ‖canonicalCGStep A g 0‖ (referencePlaneRatio A hA g) t z v)

/-- Every actual selected scalar search on the true quadratic history
reaches its genuine next reference point. The endpoint is derived from
actual scalar stationarity and true Hessian positivity.
Article: main_krylov, prop:Fcycle(iii). -/
theorem referencePlaneCubic_quadratic_search (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hN : 2≤referenceAtomCount A hA g)
    (t : krylov.Tensor.BinaryCubic) (R : ℝ) (hH : ReferencePlanePositiveBall A hA g t R)
    (m : ProbedMethod (EuclideanSpace ℝ (Fin n))) (hm : CGConsistent m)
    (i : ℕ) (hi : i<referenceAtomCount A hA g) (hnode : ‖referencePlaneNode A g (i+1)‖≤R) :
    let H := methodRun m (fun _=>cgOperator A) (fun _=>cgOperator A) g i
    metricLocalExactPoint (metricCoordinates A hA) (referencePlaneCubicObjective A hA g t)
      H.displacement (m.direction H) R=CG.displacement (cgOperator A) g (i+1) := by
  let Q := cgOperator A
  let H := methodRun m (fun _=>Q) (fun _=>Q) g i
  let α := lineLength H.gradient (m.direction H) (Q (m.direction H))
  have hpos := cgOperator_positive A hA
  have hα : 0<α := (quadratic_search_positive m hm Q hpos.1 hpos.2 g i
    (cg_nonstagnation A hA g i hi)).2
  have hstep : α • m.direction H=referenceStep Q g i := scalar_quadratic_line_step m hm Q hpos.1 hpos.2 g i
  have hx : H.displacement=CG.displacement Q g i := quadratic_displacement_eq_cg m hm Q hpos.1 hpos.2 g i
  apply metricHilbertPlaneObjective_localExactPoint (metricCoordinates A hA)
    (referencePlaneFirst A g) (referencePlaneLast A hA g) (referencePlaneComplement A hA g)
    ‖canonicalCGStep A g 0‖ (referencePlaneRatio A hA g) t R (1/2) (by norm_num)
  · intro z hz v
    have hh := hH z hz v
    nlinarith only [hh]
  · simpa only [←referencePlaneNode_metric] using hnode
  · refine ⟨α,?_⟩
    rw [hx,hstep,CG.displacement_succ]
    rfl
  · rw [←referencePlaneNode_metric]
    exact referencePlaneCubic_search_stationary A hA g hN t i hi _ α hα.ne' hstep

/-- The complete true scalar prefix of every globally CG-consistent
original policy equals its actual quadratic history. All intermediate
correction decisions and all intermediate gradient queries are replayed;
none is assumed zero as a source-class field.
Article: main_krylov, prop:Fcycle(iii). -/
theorem referencePlaneCubic_scalar_prefix (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hN : 2≤referenceAtomCount A hA g)
    (t : krylov.Tensor.BinaryCubic) (R : ℝ) (hH : ReferencePlanePositiveBall A hA g t R)
    (hnodes : ∀ i≤referenceAtomCount A hA g, ‖referencePlaneNode A g i‖≤R)
    (m : ProbedMethod (EuclideanSpace ℝ (Fin n))) (hm : CGConsistent m) :
    ∀ i≤referenceAtomCount A hA g-1,
      scalarFunctionRun m (metricCoordinates A hA) (referencePlaneCubicObjective A hA g t)
        (gradient (referencePlaneCubicObjective A hA g t)) R 0 i=
      methodRun m (fun _=>cgOperator A) (fun _=>cgOperator A) g i := by
  let Q := cgOperator A
  let f := referencePlaneCubicObjective A hA g t
  have hpos := cgOperator_positive A hA
  have hinit : gradient f 0=g := by
    have hg := referencePlaneCubicGradient_prefix A hA g hN t 0 (by omega)
    simpa only [CG.displacement,range_zero,sum_empty,CG.gradient,cgRun] using hg
  apply scalarFunctionRun_quadratic_prefix m hm (metricCoordinates A hA) f (gradient f) R 0 Q hpos.1 hpos.2 g hinit
  · intro i hi
    exact cg_nonstagnation A hA g i (by omega)
  · intro i hi
    let H := methodRun m (fun _=>Q) (fun _=>Q) g i
    let α := lineLength H.gradient (m.direction H) (Q (m.direction H))
    have hiN : i<referenceAtomCount A hA g := by omega
    have hnext : i+1<referenceAtomCount A hA g := by omega
    have hs := referencePlaneCubic_quadratic_search A hA g hN t R hH m hm i hiN (hnodes (i+1) (by omega))
    have hstep := scalar_quadratic_line_step m hm Q hpos.1 hpos.2 g i
    have hx := quadratic_displacement_eq_cg m hm Q hpos.1 hpos.2 g i
    dsimp only
    rw [zero_add,hs]
    constructor
    · rw [hx,CG.displacement_succ,add_sub_cancel_left]
      exact hstep.symm
    · rw [referencePlaneCubicGradient_prefix A hA g hN t (i+1) hnext]
      obtain ⟨_,_,_,hz⟩ := hm Q hpos.1 hpos.2 g i
      have hg := quadratic_gradient_eq_cg m hm Q hpos.1 hpos.2 g (i+1)
      change (runCorrections (m.correction H (Q (m.direction H))) Q
        (searchedGradient H.gradient (m.direction H) (Q (m.direction H)))).gradient=_ at hg
      rw [(zeroCorrections_change_operator _ Q Q _ hz).2.2] at hg
      exact hg.symm

end
end krylov.Functions
