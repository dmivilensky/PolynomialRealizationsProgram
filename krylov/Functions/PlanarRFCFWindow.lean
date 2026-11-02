import krylov.Functions.HilbertPlaneValueModel

/-!
Article: main_krylov, thm:Fplanar, actual first/middle/last model window.
Use: retain an arbitrary number of genuine middle observations; their
planar steps vanish, so the actual planar corrected model has only the
original first/last two-by-two block. Source: exact scalar model evaluation.
-/
namespace krylov.Functions
noncomputable section
open Matrix krylov.Methods krylov.Correction krylov.Tensor.BinaryCubic
open scoped InnerProductSpace
variable {ι : Type*} [Fintype ι] [LinearOrder ι] [OrderBot ι] [OrderTop ι] [DecidableEq ι]

/-- The true first/middle/last projected source anchors.
Article: main_krylov, thm:Fplanar. -/
def planeRFCFWindowAnchor (p : ℝ) (i : ι) : Plane :=
  if i=⊥ then 0 else planeOfPair (p,0)

/-- Only the first and last actual source steps have a planar component.
Article: main_krylov, thm:Fplanar. -/
def planeRFCFWindowStep (p r : ℝ) (i : ι) : Plane :=
  if i=⊥ then planeOfPair (p,0) else if i=⊤ then planeOfPair (0,r*p) else 0

set_option maxHeartbeats 1600000 in
/-- The true planar corrected model with any number of middle pairs is
exactly the compression of the original first/last observed model.
No block form is assumed. Article: main_krylov, thm:Fplanar. -/
theorem planeRFCF_window_model (hι : (⊥ : ι)≠⊤) (p r : ℝ) (t : krylov.Tensor.BinaryCubic) :
    valueCorrectedModel (planeCubicObjective p r t)
      (fun x=>innerSL ℝ (gradient (planeCubicObjective p r t) x))
      (planeRFCFWindowAnchor p : ι → Plane) (planeRFCFWindowStep p r) (fun _=>1/2)=
      correctionCompression (planeRFCFWindowStep p r : ι → Plane)
        (ContinuousLinearMap.id ℝ Plane+p • planeRFCFModelOperator r t) := by
  ext i j
  rcases le_total i j with hij | hij
  all_goals
  by_cases hi0 : i=⊥ <;> by_cases hi1 : i=⊤ <;>
    by_cases hj0 : j=⊥ <;> by_cases hj1 : j=⊤ <;>
    simp_all [valueCorrectedModel,krylov.Secant.latest,segmentValueDefect,correctionCompression,crossGram,
      planeRFCFWindowAnchor,planeRFCFWindowStep,planeRFCFModelOperator,planeCubicGradient_actual,
      planeCubicObjective,planarCubicObjective,planarReferenceQuadratic,planarValueFamily,
      planeCubicGradient,planarCubicGradient,planarValueCoordinateDerivative,planeOfPair,pairOfPlane,
      PiLp.inner_apply,Fin.sum_univ_two,ContinuousLinearMap.smulRight_apply,Matrix.diagonal,eq_comm] <;> ring

end
end krylov.Functions
