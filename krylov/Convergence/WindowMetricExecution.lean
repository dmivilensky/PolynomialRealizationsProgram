import krylov.Convergence.WindowFullValueExecution
import krylov.Functions.ObjectiveCoordinates
import krylov.Nonlinear.MetricCoordinates

/-!
Article: main_krylov, thm:Ip, thm:ss1F and thm:grow, actual metric executors.
Use: prove covariance of the observed full-window SS1 and SS1-F rules,
including their real function values and observable covector splits.
Source: true self-adjoint inverse coordinates, exact finite observed-model
solves and the established affine trapezoid identity. No FC direction
covariance is asserted: only the full observed model query is transported.
-/

namespace krylov.Convergence
noncomputable section
open Matrix krylov.Methods krylov.Functions krylov.Nonlinear
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {p : ℕ}

/-- Genuine primal and dual coordinate pairings agree under a symmetric
inverse map, independently of any algorithm or derivative source. -/
theorem inverse_symmetric_pairing (T : E ≃L[ℝ] E)
    (hT : T.symm.toContinuousLinearMap.IsSymmetric) (u v : E) :
    inner ℝ (T u) (T.symm v)=inner ℝ u v := by
  have hh := hT (T u) v
  change inner ℝ (T.symm (T u)) v=inner ℝ (T u) (T.symm v) at hh
  rw [T.symm_apply_apply] at hh
  exact hh.symm

/-- The true full SS1 query commutes with physical positive metric
coordinates, with its observed gradients transformed dually. -/
theorem ss1Point_coordinate (T : E ≃L[ℝ] E)
    (hT : T.symm.toContinuousLinearMap.IsSymmetric) (s y : Fin p → E) (g x : E) :
    T (ss1Point s y g x)=ss1Point (fun i=>T (s i)) (fun i=>T.symm (y i)) (T.symm g) (T x) := by
  have hgram : crossGram (fun i=>T (s i)) (fun i=>T.symm (y i))=crossGram s y := by
    ext i j
    exact inverse_symmetric_pairing T hT (s i) (y j)
  have hcoords : coordinates (fun i=>T (s i)) (T.symm g)=coordinates s g := by
    funext i
    exact inverse_symmetric_pairing T hT (s i) g
  simp only [ss1Point,ss1Model,hgram,modelCoefficients,hcoords,combine,map_add,map_sum,map_smul]

/-- The actual inverse-coordinate gradient represents exactly the
pulled-back physical covector; no differentiability assumption is needed
for this algebraic data identity. -/
theorem coordinateGradient_covector (T : E ≃L[ℝ] E)
    (hT : T.symm.toContinuousLinearMap.IsSymmetric) (G : E → E) (y : E) :
    innerSL ℝ (coordinateGradient T G y)=
      (innerSL ℝ (G (T.symm y))).comp T.symm.toContinuousLinearMap := by
  ext v
  exact hT (G (T.symm y)) v

/-- The genuine observed function-value model is invariant under the true
coordinate pullback, with the same actual scalar split values. -/
theorem valueCorrectedModel_coordinate (T : E ≃L[ℝ] E)
    (hT : T.symm.toContinuousLinearMap.IsSymmetric) (f : E → ℝ) (G : E → E)
    (a s : Fin p → E) (l : Fin p → ℝ) :
    valueCorrectedModel (coordinateObjective T f) (fun z=>innerSL ℝ (coordinateGradient T G z))
      (fun i=>T (a i)) (fun i=>T (s i)) l=
      valueCorrectedModel f (fun z=>innerSL ℝ (G z)) a s l := by
  have hd : (fun z=>innerSL ℝ (coordinateGradient T G z))=
      (fun z=>(innerSL ℝ (G (0+T.symm z))).comp T.symm.toContinuousLinearMap) := by
    funext z
    simpa only [zero_add] using coordinateGradient_covector T hT G z
  rw [hd]
  have hh := valueCorrectedModel_affine f (fun z=>innerSL ℝ (G z)) T.symm.toContinuousLinearMap 0
    (fun i=>T (a i)) (fun i=>T (s i)) l
  simp only [zero_add]
  change valueCorrectedModel (fun z=>f (T.symm z))
    (fun z=>(innerSL ℝ (G (T.symm z))).comp T.symm.toContinuousLinearMap)
    (fun i=>T (a i)) (fun i=>T (s i)) l=_
  simpa only [zero_add,ContinuousLinearEquiv.coe_coe,T.symm_apply_apply] using hh

/-- The true full value-corrected SS1-F query commutes with genuine metric
coordinates, including all original endpoint values and actual gradients. -/
theorem ss1FPoint_coordinate (T : E ≃L[ℝ] E)
    (hT : T.symm.toContinuousLinearMap.IsSymmetric) (f : E → ℝ) (G : E → E)
    (a s : Fin p → E) (l : Fin p → ℝ) (x : E) :
    T (ss1FPoint f G a s l x)=ss1FPoint (coordinateObjective T f) (coordinateGradient T G)
      (fun i=>T (a i)) (fun i=>T (s i)) l (T x) := by
  have hcoords : coordinates (fun i=>T (s i)) (T.symm (G x))=coordinates s (G x) := by
    funext i
    exact inverse_symmetric_pairing T hT (s i) (G x)
  simp only [ss1FPoint]
  rw [valueCorrectedModel_coordinate T hT f G a s l]
  simp only [coordinateGradient,T.symm_apply_apply,modelCoefficients,hcoords,combine,map_add,map_sum,map_smul]

/-- The actual model-metric split is invariant under the genuine primal
and dual coordinate change; all quantities remain observed scalars. -/
theorem covectorSplit_coordinate (T : E ≃L[ℝ] E)
    (hT : T.symm.toContinuousLinearMap.IsSymmetric) (y a s x : E) :
    covectorSplit (innerSL ℝ (T.symm y)) (T a) (T s) (T x)=covectorSplit (innerSL ℝ y) a s x := by
  have he : (innerSL ℝ (T.symm y)).comp T.toContinuousLinearMap=innerSL ℝ y := by
    ext v
    exact (real_inner_comm _ _).trans ((inverse_symmetric_pairing T hT v y).trans (real_inner_comm _ _))
  have hh := covectorSplit_affine (innerSL ℝ (T.symm y)) T.toContinuousLinearMap 0 a s x
  simpa only [he,zero_add,ContinuousLinearEquiv.coe_coe] using hh.symm

/-- The observable split policy of the genuine SS1-F executor transports
exactly with the actual endpoint gradient observations. -/
theorem ss1FObservedSplit_coordinate {n : ℕ} (T : E ≃L[ℝ] E)
    (hT : T.symm.toContinuousLinearMap.IsSymmetric) (G : E → E) (q : Fin (n+2) → E) :
    ss1FObservedSplit (coordinateGradient T G) (fun i=>T (q i))=ss1FObservedSplit G q := by
  funext i
  simp only [ss1FObservedSplit,coordinateGradient,T.symm_apply_apply,←map_sub]
  simpa only [map_sub] using covectorSplit_coordinate T hT
    (G (q i.succ)-G (q i.castSucc)) (q i.castSucc) (q i.succ-q i.castSucc) (q (Fin.last (n+1)))

/-- The genuine one-gradient SS1 window rule transports exactly through
metric coordinates, using the true observed endpoint gradients. -/
theorem ss1WindowRule_coordinate {n : ℕ} (T : E ≃L[ℝ] E)
    (hT : T.symm.toContinuousLinearMap.IsSymmetric) (G : E → E) (q : Fin (n+2) → E) :
    T (ss1WindowRule G q)=ss1WindowRule (coordinateGradient T G) (fun i=>T (q i)) := by
  have hh := ss1Point_coordinate T hT (fun i : Fin (n+1)=>q i.succ-q i.castSucc)
    (fun i=>G (q i.succ)-G (q i.castSucc)) (G (q (Fin.last (n+1)))) (q (Fin.last (n+1)))
  simpa only [ss1WindowRule,coordinateGradient,T.symm_apply_apply,map_sub] using hh

/-- The genuine observable SS1-F rule transports exactly, including its
actual data-dependent model-metric split and endpoint values. -/
theorem ss1FWindowRule_coordinate {n : ℕ} (T : E ≃L[ℝ] E)
    (hT : T.symm.toContinuousLinearMap.IsSymmetric) (f : E → ℝ) (G : E → E) (q : Fin (n+2) → E) :
    T (ss1FWindowRule f G (ss1FObservedSplit G) q)=
      ss1FWindowRule (coordinateObjective T f) (coordinateGradient T G)
        (ss1FObservedSplit (coordinateGradient T G)) (fun i=>T (q i)) := by
  simp only [ss1FWindowRule]
  rw [ss1FObservedSplit_coordinate T hT G q]
  have hh := ss1FPoint_coordinate T hT f G (fun i : Fin (n+1)=>q i.castSucc)
    (fun i=>q i.succ-q i.castSucc) (ss1FObservedSplit G q) (q (Fin.last (n+1)))
  simpa only [map_sub] using hh

/-- The literal SS1 recursive executor commutes with actual metric
coordinates, with its own genuinely transformed initial window. -/
theorem ss1Sequence_coordinate {n : ℕ} (T : E ≃L[ℝ] E)
    (hT : T.symm.toContinuousLinearMap.IsSymmetric) (G : E → E) (seed : Fin (n+2) → E) (j : ℕ) :
    T (ss1Sequence G seed j)=ss1Sequence (coordinateGradient T G) (fun i=>T (seed i)) j := by
  let x := fun k=>T (ss1Sequence G seed k)
  have hstep (k : ℕ) : x (k+n+2)=ss1WindowRule (n:=n) (coordinateGradient T G) (fun i=>x (k+i.val)) := by
    change T (slidingSequence (ss1WindowRule G) seed (k+n+2))=_
    rw [slidingSequence_step]
    exact ss1WindowRule_coordinate T hT G _
  have hh := slidingSequence_shift_eq (ss1WindowRule (coordinateGradient T G)) x 0 (fun k _=>hstep k) j
  have hseed : (fun i : Fin (n+2)=>x (0+i.val))=(fun i=>T (seed i)) := by
    funext i
    dsimp only [x]
    rw [Nat.zero_add,ss1Sequence,slidingSequence_seed]
  rw [Nat.zero_add,hseed] at hh
  exact hh

/-- The genuine observable SS1-F recursive executor commutes with actual
metric coordinates; its split policy remains entirely data-only. -/
theorem ss1FObservedSequence_coordinate {n : ℕ} (T : E ≃L[ℝ] E)
    (hT : T.symm.toContinuousLinearMap.IsSymmetric) (f : E → ℝ) (G : E → E)
    (seed : Fin (n+2) → E) (j : ℕ) :
    T (ss1FSequence f G (ss1FObservedSplit G) seed j)=
      ss1FSequence (coordinateObjective T f) (coordinateGradient T G)
        (ss1FObservedSplit (coordinateGradient T G)) (fun i=>T (seed i)) j := by
  let x := fun k=>T (ss1FSequence f G (ss1FObservedSplit G) seed k)
  have hstep (k : ℕ) : x (k+n+2)=
      ss1FWindowRule (n:=n) (coordinateObjective T f) (coordinateGradient T G)
        (ss1FObservedSplit (coordinateGradient T G)) (fun i=>x (k+i.val)) := by
    change T (slidingSequence (ss1FWindowRule f G (ss1FObservedSplit G)) seed (k+n+2))=_
    rw [slidingSequence_step]
    exact ss1FWindowRule_coordinate T hT f G _
  have hh := slidingSequence_shift_eq
    (ss1FWindowRule (coordinateObjective T f) (coordinateGradient T G) (ss1FObservedSplit (coordinateGradient T G)))
    x 0 (fun k _=>hstep k) j
  have hseed : (fun i : Fin (n+2)=>x (0+i.val))=(fun i=>T (seed i)) := by
    funext i
    dsimp only [x]
    rw [Nat.zero_add,ss1FSequence,slidingSequence_seed]
  rw [Nat.zero_add,hseed] at hh
  exact hh

end
end krylov.Convergence
