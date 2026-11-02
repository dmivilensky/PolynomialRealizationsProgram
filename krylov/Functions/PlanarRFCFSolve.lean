import krylov.Functions.PlanarRFCFModel
import krylov.Methods.VirtualSolve

/-!
Article: main_krylov, thm:Fplanar, the genuine observed RFC-F solve.
Use: execute the actual value-corrected model on the true first/last scalar
source observations and derive its normal equations and correction bound.
Source: the proved actual model compression and the implemented matrix solve.
-/
namespace krylov.Functions
noncomputable section
open Set Metric Matrix krylov.Tensor.BinaryCubic krylov.Methods krylov.Correction
open scoped InnerProductSpace BigOperators Matrix.Norms.L2Operator

/-- The true observed last value-model correction, using no tensor or Hessian.
Article: main_krylov, thm:Fplanar, RFC-F model-metric split. -/
def planeRFCFCorrection (p r : ℝ) (t : krylov.Tensor.BinaryCubic) : Plane :=
  combine (planeRFCFSteps p r) (modelCoefficients (planeRFCFSteps p r)
    (valueCorrectedModel (planeCubicObjective p r t)
      (fun x=>innerSL ℝ (gradient (planeCubicObjective p r t) x))
      (planeRFCFAnchors p) (planeRFCFSteps p r) (planeRFCFSplit p r t))
    (gradient (planeCubicObjective p r t) (planeOfPair (p,r*p))))

/-- The actual RFC-F final output from the genuine scalar-source observations.
Article: main_krylov, thm:Fplanar. -/
def planeRFCFOutput (p r : ℝ) (t : krylov.Tensor.BinaryCubic) : Plane :=
  planeOfPair (p,r*p)+planeRFCFCorrection p r t

/-- The true first/last source steps are independent whenever both lengths
are nonzero. Article: main_krylov, thm:Fplanar. -/
theorem planeRFCFSteps_independent (p r : ℝ) (hp : p≠0) (hr : r≠0) :
    LinearIndependent ℝ (planeRFCFSteps p r) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have h0 := congrArg (fun v : Plane=>v 0) hc
  have h1 := congrArg (fun v : Plane=>v 1) hc
  simp [planeRFCFSteps,planeOfPair,Fin.sum_univ_two,hp,hr] at h0 h1
  fin_cases i
  · exact h0
  · exact h1

/-- Vanishing true first/last coordinates force the physical vector to vanish.
Article: main_krylov, thm:Fplanar, full observed span. -/
theorem planeRFCFSteps_coordinates_zero (p r : ℝ) (hp : p≠0) (hr : r≠0)
    (v : Plane) (hv : coordinates (planeRFCFSteps p r) v=0) : v=0 := by
  have h0 := congrFun hv 0
  have h1 := congrFun hv 1
  simp [coordinates,planeRFCFSteps,planeOfPair,PiLp.inner_apply,Fin.sum_univ_two,hp,hr] at h0 h1
  ext i
  fin_cases i
  · exact h0
  · exact h1

/-- The actual observed normalized model is symmetric.
Article: main_krylov, thm:Fplanar. -/
theorem planeRFCFModelOperator_symmetric (r : ℝ) (t : krylov.Tensor.BinaryCubic) :
    (planeRFCFModelOperator r t).toLinearMap.IsSymmetric := by
  intro u v
  simp [planeRFCFModelOperator,planeOfPair,PiLp.inner_apply,Fin.sum_univ_two]
  ring

/-- The genuine model compression is nonsingular and the implemented
last correction solves the exact full physical model equation.
Article: main_krylov, thm:Fplanar, actual RFC-F update. -/
theorem planeRFCFCorrection_equation (p r : ℝ) (hp : p≠0) (hr : r≠0)
    (t : krylov.Tensor.BinaryCubic)
    (hpos : ∀ v : Plane, v≠0 → 0 < inner ℝ v
      ((ContinuousLinearMap.id ℝ Plane+p • planeRFCFModelOperator r t) v)) :
    planeRFCFCorrection p r t+p • planeRFCFModelOperator r t (planeRFCFCorrection p r t)=
      -p^2 • planeTerminalRho r t := by
  let Q := ContinuousLinearMap.id ℝ Plane+p • planeRFCFModelOperator r t
  have hQ : Q.toLinearMap.IsSymmetric := (by intro u v; rfl : (ContinuousLinearMap.id ℝ Plane).toLinearMap.IsSymmetric).add
    ((planeRFCFModelOperator_symmetric r t).smul (by simp : (starRingEnd ℝ) p=p))
  have hH : IsUnit (correctionCompression (planeRFCFSteps p r) Q).det := by
    have hh := operatorGram_posDef Q hQ hpos (planeRFCFSteps_independent p r hp hr)
    have he : crossGram (fun i=>Q (planeRFCFSteps p r i)) (planeRFCFSteps p r)=
        correctionCompression (planeRFCFSteps p r) Q := by
      ext i j
      exact hQ _ _
    exact isUnit_iff_ne_zero.mpr ((he ▸ hh).det_pos.ne')
  have hh := modelCorrection_projected (planeRFCFSteps p r)
    (correctionCompression (planeRFCFSteps p r) Q) hH Q
    (gradient (planeCubicObjective p r t) (planeOfPair (p,r*p)))
  simp only [sub_self,zero_mul,neg_zero,zero_mulVec] at hh
  have hg : gradient (planeCubicObjective p r t) (planeOfPair (p,r*p))=p^2 • planeTerminalRho r t := by
    have he := planeCubicGradient_terminal_identity p r t (0 : Plane)
    have hz : planeOfPair (0,0)=0 := by ext i; fin_cases i <;> rfl
    simpa [planarValueCoordinateDerivative,pairOfPlane,hz] using he
  have hv := planeRFCFSteps_coordinates_zero p r hp hr _ hh
  rw [hg] at hv
  change p^2 • planeTerminalRho r t+Q _=0 at hv
  have hcorr : combine (planeRFCFSteps p r)
      (modelCoefficients (planeRFCFSteps p r) (correctionCompression (planeRFCFSteps p r) Q)
        (p^2 • planeTerminalRho r t))=planeRFCFCorrection p r t := by
    unfold planeRFCFCorrection
    rw [planeRFCF_observed_model p r hp hr t,hg]
  rw [hcorr] at hv
  simpa only [Q,_root_.add_apply,_root_.smul_apply,ContinuousLinearMap.id_apply,neg_smul] using
    eq_neg_of_add_eq_zero_right hv

end
end krylov.Functions
