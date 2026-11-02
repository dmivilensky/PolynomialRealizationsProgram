import krylov.Functions.PlanarRFCFSolve
import krylov.Functions.HilbertPlaneObjective

/-!
Article: main_krylov, thm:Fplanar, the independent unknown base diagonal.
Use: keep the h-diagonal perturbation independent of the cubic coefficients.
The actual scalar objective, its Riesz gradient, its observed model-metric
splits and its complete value-corrected model are computed explicitly.
Source: true scalar differentiation and exact quadratic trapezoid cancellation.
-/
namespace krylov.Functions
noncomputable section
open Matrix krylov.Methods krylov.Correction krylov.Tensor.BinaryCubic
open scoped InnerProductSpace Matrix.Norms.L2Operator

/-- The actual scalar source with an independent unknown quadratic diagonal.
The added quadratic is centered at the last searched point, so it changes
both the true Hessian and the actual reconstructed model by the same term.
Article: main_krylov, thm:Fplanar, independent beta. -/
def planeBetaCubicObjective (p r β : ℝ) (t : krylov.Tensor.BinaryCubic) (x : Plane) : ℝ :=
  planeCubicObjective p r t x+β/2*(x 1-r*p)^2

/-- The genuine h-diagonal rank-one operator. Article: thm:Fplanar. -/
def planeLastProjection : Plane →L[ℝ] Plane :=
  (EuclideanSpace.proj 1).smulRight (planeOfPair (0,1))

/-- The mathematical gradient of the independent-base scalar source.
Article: main_krylov, thm:Fplanar. -/
theorem planeBetaCubicGradient_actual (p r β : ℝ) (t : krylov.Tensor.BinaryCubic) (x : Plane) :
    gradient (planeBetaCubicObjective p r β t) x=
      gradient (planeCubicObjective p r t) x+(β*(x 1-r*p)) • planeOfPair (0,1) := by
  have hb := (planeCubicObjective_differentiable p r t x).hasGradientAt.hasFDerivAt
  have hy := ((EuclideanSpace.proj (𝕜:=ℝ) (ι:=Fin 2) 1).hasFDerivAt (x:=x)).sub_const (r*p)
  have hd := hb.add ((hy.pow 2).const_mul (β/2))
  apply (hasGradientAt_iff_hasFDerivAt.mpr ?_).gradient
  convert! hd using 1
  ext v
  simp [planeOfPair,PiLp.inner_apply,Fin.sum_univ_two]
  ring

/-- Actual model-metric splits for the independent-base source.
Article: thm:Fplanar. -/
def planeBetaRFCFSplit (p r β : ℝ) (t : krylov.Tensor.BinaryCubic) (i : Fin 2) : ℝ :=
  let G := gradient (planeBetaCubicObjective p r β t)
  let a := planeRFCFAnchors p i
  let s := planeRFCFSteps p r i
  covectorSplit (innerSL ℝ (G (a+s)-G a)) a s (planeOfPair (p,r*p))

/-- The independent diagonal does not change the genuine observed split.
Article: main_krylov, thm:Fplanar. -/
theorem planeBetaRFCFSplit_eq_half (p r β : ℝ) (hp : p≠0) (hr : r≠0)
    (hβ : 1+β≠0) (t : krylov.Tensor.BinaryCubic) (i : Fin 2) :
    planeBetaRFCFSplit p r β t i=1/2 := by
  fin_cases i <;>
    simp [planeBetaRFCFSplit,covectorSplit,planeRFCFAnchors,planeRFCFSteps,
      planeBetaCubicGradient_actual,planeCubicGradient_actual,
      planeCubicGradient,planarCubicGradient,planarValueCoordinateDerivative,planeOfPair,pairOfPlane,
      PiLp.inner_apply,Fin.sum_univ_two] <;> ring_nf <;> field_simp [hp,hr,hβ]
  all_goals ring

set_option maxHeartbeats 1000000 in
/-- The actual full value-corrected model reconstructs the independent base
quadratic exactly; it is not completed by any hidden tensor coefficient.
Article: main_krylov, thm:Fplanar, all independent beta. -/
theorem planeBetaRFCF_observed_model (p r β : ℝ) (hp : p≠0) (hr : r≠0)
    (hβ : 1+β≠0) (t : krylov.Tensor.BinaryCubic) :
    valueCorrectedModel (planeBetaCubicObjective p r β t)
      (fun x=>innerSL ℝ (gradient (planeBetaCubicObjective p r β t) x))
      (planeRFCFAnchors p) (planeRFCFSteps p r) (planeBetaRFCFSplit p r β t)=
      correctionCompression (planeRFCFSteps p r)
        (ContinuousLinearMap.id ℝ Plane+p • planeRFCFModelOperator r t+β • planeLastProjection) := by
  have hl : planeBetaRFCFSplit p r β t=fun _=>1/2 := funext (planeBetaRFCFSplit_eq_half p r β hp hr hβ t)
  rw [hl]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [valueCorrectedModel,krylov.Secant.latest,segmentValueDefect,correctionCompression,crossGram,
      planeRFCFAnchors,planeRFCFSteps,planeRFCFModelOperator,planeBetaCubicGradient_actual,planeCubicGradient_actual,
      planeBetaCubicObjective,planeLastProjection,planeCubicObjective,planarCubicObjective,planarReferenceQuadratic,planarValueFamily,
      planeCubicGradient,planarCubicGradient,planarValueCoordinateDerivative,planeOfPair,pairOfPlane,
      PiLp.inner_apply,Fin.sum_univ_two,ContinuousLinearMap.smulRight_apply] <;> ring

/-- The unknown diagonal cancels identically from the true-model discrepancy.
Article: main_krylov, thm:Fplanar, why C_Y is uniform in independent beta. -/
theorem planeBetaRFCF_discrepancy (r b : ℝ) (t : krylov.Tensor.BinaryCubic) :
    (planeTerminalOperator r t+b • planeLastProjection)-
      (planeRFCFModelOperator r t+b • planeLastProjection)=
        planeTerminalOperator r t-planeRFCFModelOperator r t := by abel

end
end krylov.Functions
