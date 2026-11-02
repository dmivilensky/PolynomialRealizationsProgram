import krylov.Functions.ReferencePlaneRFCFPrefix
import krylov.Methods.ReferenceModels

/-!
Article: main_krylov, thm:Fplanar, literal native RFC-F full observations.
Use: retain every actual native anchor, total old step and final searched
segment. Their genuine scalar source replay gives the exact original CG
window, common last endpoint and accepted original observed gate.
Source: native complete-history replay, actual scalar search stationarity
and quadratic symmetry of the real stored prefix.
-/
namespace krylov.Functions
noncomputable section
open Matrix Finset krylov.Reference krylov.Tensor krylov.Nonlinear krylov.Methods
open scoped InnerProductSpace BigOperators Matrix.Norms.L2Operator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {n k : ℕ}

/-- The genuine static full-memory RFC prefix has an accepted old-pair
gate after every positive number of steps.
Article: main_krylov, thm:Fplanar, actual native gate domain. -/
theorem rfcFunctionGate_quadratic (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v)) (g : E) (k : ℕ) (hk : 0<k) :
    rfcFunctionGate fullMemory
      (methodRun (rfcMethod fullMemory 1) (fun _=>Q) (fun _=>Q) g k) := by
  let H := methodRun (rfcMethod fullMemory 1) (fun _=>Q) (fun _=>Q) g k
  have ht := rfcMethod_static fullMemory 1 Q hQ hpos g (fun _ _ ha=>ha) k
  have hl : H.records.length=k := by rw [←H.pairs_length,ht.2,referencePairs_length]
  have hW : selectedWindow fullMemory H=(referencePairs Q g k).take k := by
    unfold selectedWindow
    rw [hl,ht.2]
    rfl
  have hne : (referencePairs Q g k).take k≠[] := by
    intro hz
    have hh := congrArg List.length hz
    simp only [List.length_take,referencePairs_length,min_self,List.length_nil] at hh
    omega
  unfold rfcFunctionGate
  rw [hW,windowDefect_quadratic _ Q hQ (retainedImages_quadratic Q g k k),norm_zero]
  exact ⟨hne,zero_lt_one⟩

set_option maxHeartbeats 1000000 in
/-- Every actual native RFC-F retained observation is its genuine original
reference node or step, and its actual final model gate is accepted.
The final search is the real scalar objective search, not a prescribed point.
Article: main_krylov, thm:Fplanar, literal full executor data dictionary. -/
theorem referencePlaneCubic_rfcF_observations
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) (g : EuclideanSpace ℝ (Fin n))
    (hc : referenceAtomCount A hA g=k+2)
    (t : krylov.Tensor.BinaryCubic) (R : ℝ) (hH : ReferencePlanePositiveBall A hA g t R)
    (hnodes : ∀ i≤referenceAtomCount A hA g, ‖referencePlaneNode A g i‖≤R) :
    let T := metricCoordinates A hA
    let f := referencePlaneCubicObjective A hA g t
    let G := gradient f
    (∀ i : Fin (k+2), rfcFAnchors T f G R 0 (k+1) i=CG.displacement (cgOperator A) g i.val) ∧
    (∀ i : Fin (k+2), rfcFSteps T f G R 0 (k+1) i=referenceStep (cgOperator A) g i.val) ∧
    rfcFAnchor T f G R 0 (k+1)=CG.displacement (cgOperator A) g (k+2) ∧
    rfcFunctionGate fullMemory (rfcFunctionRun T f G fullMemory R 0 (k+1)) := by
  let T := metricCoordinates A hA
  let f := referencePlaneCubicObjective A hA g t
  let G := gradient f
  let Q := cgOperator A
  let m := rfcMethod fullMemory 1 (E:=EuclideanSpace ℝ (Fin n))
  have hm := rfcMethod_consistent fullMemory (fun _ ha=>ha) 1 (E:=EuclideanSpace ℝ (Fin n))
  have hpos := cgOperator_positive A hA
  have hN : 2≤referenceAtomCount A hA g := by omega
  have hprefix := referencePlaneCubic_rfc_prefix A hA g hN t R hH hnodes
  have hpoint i (hi : i≤k+1) : rfcFunctionPoint T f G fullMemory R 0 i=CG.displacement Q g i := by
    unfold rfcFunctionPoint
    rw [hprefix i (by omega),zero_add]
    exact quadratic_displacement_eq_cg m hm Q hpos.1 hpos.2 g i
  have hline i (hi : i≤k+1) :
      rfcFunctionLinePoint T f fullMemory R 0 (rfcFunctionRun T f G fullMemory R 0 i)=
        CG.displacement Q g (i+1) := by
    rw [hprefix i (by omega)]
    have hs := referencePlaneCubic_quadratic_search A hA g hN t R hH m hm i (by omega)
      (hnodes (i+1) (by omega))
    simpa only [rfcFunctionLinePoint,zero_add] using! hs
  have hanchors (i : Fin (k+2)) : rfcFAnchors T f G R 0 (k+1) i=CG.displacement Q g i.val :=
    hpoint i.val (by omega)
  have hsteps (i : Fin (k+2)) : rfcFSteps T f G R 0 (k+1) i=referenceStep Q g i.val := by
    by_cases hi : i.val<k+1
    · simp only [rfcFSteps,ite_eq_left hi,hanchors,hpoint (i.val+1) (by omega)]
      rw [CG.displacement_succ]
      abel
    · have hit : i.val=k+1 := by omega
      rw [rfcFSteps,ite_eq_right hi]
      rw [hit]
      simp only [rfcFunctionLineStep,hline (k+1) le_rfl,zero_add]
      rw [show (rfcFunctionRun T f G fullMemory R 0 (k+1)).displacement=CG.displacement Q g (k+1) by
        simpa only [rfcFunctionPoint,zero_add] using hpoint (k+1) le_rfl,CG.displacement_succ]
      abel
  refine ⟨hanchors,hsteps,hline (k+1) le_rfl,?_⟩
  rw [hprefix (k+1) (by omega)]
  exact rfcFunctionGate_quadratic Q hpos.1 hpos.2 g (k+1) (by omega)

end
end krylov.Functions
