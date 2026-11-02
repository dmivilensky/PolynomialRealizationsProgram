import krylov.Functions.PlanarPolicyTaylor
import krylov.Functions.ValueModelCoordinates
import krylov.Tensor.BinaryRFC

/-!
Article: main_krylov, thm:Fplanar, actual RFC-F planar model.
Use: compute the model-metric split and corrected model directly from the
true values and gradients of the complete scalar cubic source family.
Source: the actual observed trapezoid model and exact polynomial identities.
-/
namespace krylov.Functions
noncomputable section
open Set Metric Matrix krylov.Tensor.BinaryCubic krylov.Methods krylov.Correction
open scoped InnerProductSpace Matrix.Norms.L2Operator

/-- The genuine first and last observed planar anchors.
Article: main_krylov, thm:Fplanar. -/
def planeRFCFAnchors (p : ℝ) : Fin 2 → Plane := ![0,planeOfPair (p,0)]

/-- The genuine chronological first and last reference segments.
Article: main_krylov, thm:Fplanar. -/
def planeRFCFSteps (p r : ℝ) : Fin 2 → Plane := ![planeOfPair (p,0),planeOfPair (0,r*p)]

/-- The split computed from the actual scalar source gradients.
Article: main_krylov, thm:Fplanar, lambda^Y. -/
def planeRFCFSplit (p r : ℝ) (t : krylov.Tensor.BinaryCubic) (i : Fin 2) : ℝ :=
  let G := gradient (planeCubicObjective p r t)
  let a := planeRFCFAnchors p i
  let s := planeRFCFSteps p r i
  covectorSplit (innerSL ℝ (G (a+s)-G a)) a s (planeOfPair (p,r*p))

/-- The true observed model-metric splits equal one-half exactly.
Article: main_krylov, thm:Fplanar, later steps orthogonal to the first secant. -/
theorem planeRFCFSplit_eq_half (p r : ℝ) (hp : p≠0) (hr : r≠0)
    (t : krylov.Tensor.BinaryCubic) (i : Fin 2) : planeRFCFSplit p r t i=1/2 := by
  fin_cases i <;>
    simp [planeRFCFSplit,covectorSplit,planeRFCFAnchors,planeRFCFSteps,planeCubicGradient_actual,
      planeCubicGradient,planarCubicGradient,planarValueCoordinateDerivative,planeOfPair,pairOfPlane,
      PiLp.inner_apply,Fin.sum_univ_two] <;> ring_nf <;> field_simp [hp,hr]

/-- The physical normalized model perturbation computed from the true
observed values, with no hidden coefficient completion.
Article: main_krylov, thm:Fplanar, model-metric split. -/
def planeRFCFModelOperator (r : ℝ) (t : krylov.Tensor.BinaryCubic) : Plane →L[ℝ] Plane :=
  (EuclideanSpace.proj (𝕜:=ℝ) (ι:=Fin 2) 0).smulRight
    (planeOfPair (t.t0/2,(t.t1+r*t.t2)/2))+
  (EuclideanSpace.proj (𝕜:=ℝ) (ι:=Fin 2) 1).smulRight
    (planeOfPair ((t.t1+r*t.t2)/2,r*t.t3/2))

set_option maxHeartbeats 1000000 in
/-- The actual value-and-gradient model is exactly the compression of the
printed normalized planar model, including both genuine observed defects.
Article: main_krylov, thm:Fplanar, the full source-to-model dictionary. -/
theorem planeRFCF_observed_model (p r : ℝ) (hp : p≠0) (hr : r≠0)
    (t : krylov.Tensor.BinaryCubic) :
    valueCorrectedModel (planeCubicObjective p r t)
      (fun x=>innerSL ℝ (gradient (planeCubicObjective p r t) x))
      (planeRFCFAnchors p) (planeRFCFSteps p r) (planeRFCFSplit p r t)=
      correctionCompression (planeRFCFSteps p r)
        (ContinuousLinearMap.id ℝ Plane+p • planeRFCFModelOperator r t) := by
  have hl : planeRFCFSplit p r t=fun _=>1/2 := funext (planeRFCFSplit_eq_half p r hp hr t)
  rw [hl]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [valueCorrectedModel,krylov.Secant.latest,segmentValueDefect,correctionCompression,crossGram,
      planeRFCFAnchors,planeRFCFSteps,planeRFCFModelOperator,planeCubicGradient_actual,
      planeCubicObjective,planarCubicObjective,planarReferenceQuadratic,planarValueFamily,
      planeCubicGradient,planarCubicGradient,planarValueCoordinateDerivative,planeOfPair,pairOfPlane,
      PiLp.inner_apply,Fin.sum_univ_two,ContinuousLinearMap.smulRight_apply] <;> ring

/-- The full model error's actual first column is the printed pair
(r B,r C/2). Article: main_krylov, thm:Fplanar, RFC-F response dictionary. -/
theorem planeRFCF_first_column (r : ℝ) (t : krylov.Tensor.BinaryCubic) :
    (planeTerminalOperator r t-planeRFCFModelOperator r t) (planeOfPair (1,0))=
      planeOfPair (r*t.t1,r*t.t2/2) := by
  ext i
  fin_cases i <;> simp [planeTerminalOperator,planeRFCFModelOperator,planeOfPair,
    ContinuousLinearMap.smulRight_apply]; ring

/-- The true model discrepancy applied to the actual post-search source
gradient has exactly the RFC-F polynomial leading response.
Article: main_krylov, thm:Fplanar, C_Y source dictionary. -/
theorem planeRFCF_leading_response (r : ℝ) (t : krylov.Tensor.BinaryCubic) :
    (planeTerminalOperator r t-planeRFCFModelOperator r t) (planeTerminalRho r t)=
      (r^2*(t.t1+r*t.t2)/4) • planeOfPair (2*t.t1,t.t2) := by
  ext i
  fin_cases i <;> simp [planeTerminalOperator,planeRFCFModelOperator,planeTerminalRho,planeOfPair,
    ContinuousLinearMap.smulRight_apply] <;> ring

/-- The actual response norm is the original supremum objective, with the
exact scalar normalization. Article: main_krylov, thm:Fplanar, C_Y. -/
theorem planeRFCF_leading_norm (r : ℝ) (t : krylov.Tensor.BinaryCubic) :
    ‖(planeTerminalOperator r t-planeRFCFModelOperator r t) (planeTerminalRho r t)‖=
      r^2/4*rfcObjective r t := by
  rw [planeRFCF_leading_response,norm_smul,Real.norm_eq_abs,abs_div,abs_mul,
    abs_of_nonneg (sq_nonneg r)]
  have hn : ‖planeOfPair (2*t.t1,t.t2)‖=Real.sqrt (4*t.t1^2+t.t2^2) := by
    have he : ‖planeOfPair (2*t.t1,t.t2)‖^2=4*t.t1^2+t.t2^2 := by
      simpa only [planeOfPair] using
        (plane_norm_sq (planeOfPair (2*t.t1,t.t2))).trans (by simp [planeOfPair]; ring)
    rw [←he,Real.sqrt_sq (norm_nonneg _)]
  rw [hn]
  norm_num only [show |(4:ℝ)|=4 by norm_num]
  unfold rfcObjective
  ring

end
end krylov.Functions
