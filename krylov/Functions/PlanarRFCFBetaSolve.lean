import krylov.Functions.PlanarRFCFBetaModel

/-!
Article: main_krylov, thm:Fplanar, actual independent-base correction solve.
Use: prove the implemented endpoint-value solve normal equations and true
terminal gradient identity before estimating any response.
Source: the true observed model, positive Galerkin uniqueness and exact
cubic differentiation. The unknown diagonal is an independent input.
-/
namespace krylov.Functions
noncomputable section
open Matrix krylov.Methods krylov.Correction krylov.Tensor.BinaryCubic
open scoped InnerProductSpace Matrix.Norms.L2Operator

/-- The literal observed RFC-F correction for the independent-base source.
Article: main_krylov, thm:Fplanar. -/
def planeBetaRFCFCorrection (p r β : ℝ) (t : krylov.Tensor.BinaryCubic) : Plane :=
  combine (planeRFCFSteps p r) (modelCoefficients (planeRFCFSteps p r)
    (valueCorrectedModel (planeBetaCubicObjective p r β t)
      (fun x=>innerSL ℝ (gradient (planeBetaCubicObjective p r β t) x))
      (planeRFCFAnchors p) (planeRFCFSteps p r) (planeBetaRFCFSplit p r β t))
    (gradient (planeBetaCubicObjective p r β t) (planeOfPair (p,r*p))))

/-- The actual observed RFC-F output, retaining independent beta.
Article: main_krylov, thm:Fplanar. -/
def planeBetaRFCFOutput (p r β : ℝ) (t : krylov.Tensor.BinaryCubic) : Plane :=
  planeOfPair (p,r*p)+planeBetaRFCFCorrection p r β t

/-- The real terminal gradient gains exactly the same unknown diagonal as
the observed model, while its observed right-hand side is unchanged.
Article: main_krylov, thm:Fplanar, true source-to-model dictionary. -/
theorem planeBetaCubicGradient_terminal_identity (p r β : ℝ) (t : krylov.Tensor.BinaryCubic) (v : Plane) :
    gradient (planeBetaCubicObjective p r β t) (planeOfPair (p,r*p)+v)=
      p^2 • planeTerminalRho r t+v+p • planeTerminalOperator r t v+
        β • planeLastProjection v+
        planeOfPair (planarValueCoordinateDerivative 0 r t (pairOfPlane v)) := by
  rw [planeBetaCubicGradient_actual,planeCubicGradient_terminal_identity]
  simp only [planeLastProjection,ContinuousLinearMap.smulRight_apply]
  simp [planeOfPair,smul_smul]
  abel

/-- The independent diagonal operator is truly symmetric.
Article: main_krylov, thm:Fplanar. -/
theorem planeLastProjection_symmetric : planeLastProjection.toLinearMap.IsSymmetric := by
  intro u v
  simp [planeLastProjection,planeOfPair,PiLp.inner_apply,Fin.sum_univ_two]

/-- The actual complete model solve obeys its genuine full physical normal
equation. Its domain follows from positive curvature, not an assumed inverse.
Article: main_krylov, thm:Fplanar, all independent unknown bases. -/
theorem planeBetaRFCFCorrection_equation (p r b : ℝ) (hp : p≠0) (hr : r≠0)
    (hβ : 1+p*b≠0) (t : krylov.Tensor.BinaryCubic)
    (hpos : ∀ v : Plane, v≠0 → 0 < inner ℝ v
      ((ContinuousLinearMap.id ℝ Plane+p • (planeRFCFModelOperator r t+b • planeLastProjection)) v)) :
    planeBetaRFCFCorrection p r (p*b) t+
      p • (planeRFCFModelOperator r t+b • planeLastProjection) (planeBetaRFCFCorrection p r (p*b) t)=
      -p^2 • planeTerminalRho r t := by
  let W := planeRFCFModelOperator r t+b • planeLastProjection
  let Q := ContinuousLinearMap.id ℝ Plane+p • W
  have hW : W.toLinearMap.IsSymmetric := (planeRFCFModelOperator_symmetric r t).add
    (planeLastProjection_symmetric.smul (by simp : (starRingEnd ℝ) b=b))
  have hQ : Q.toLinearMap.IsSymmetric := (by intro u v; rfl : (ContinuousLinearMap.id ℝ Plane).toLinearMap.IsSymmetric).add
    (hW.smul (by simp : (starRingEnd ℝ) p=p))
  have hH : IsUnit (correctionCompression (planeRFCFSteps p r) Q).det := by
    have hh := operatorGram_posDef Q hQ hpos (planeRFCFSteps_independent p r hp hr)
    have he : crossGram (fun i=>Q (planeRFCFSteps p r i)) (planeRFCFSteps p r)=
        correctionCompression (planeRFCFSteps p r) Q := by
      ext i j
      exact hQ _ _
    exact isUnit_iff_ne_zero.mpr ((he ▸ hh).det_pos.ne')
  have hh := modelCorrection_projected (planeRFCFSteps p r)
    (correctionCompression (planeRFCFSteps p r) Q) hH Q
    (gradient (planeBetaCubicObjective p r (p*b) t) (planeOfPair (p,r*p)))
  simp only [sub_self,zero_mul,neg_zero,zero_mulVec] at hh
  have hg : gradient (planeBetaCubicObjective p r (p*b) t) (planeOfPair (p,r*p))=p^2 • planeTerminalRho r t := by
    have he := planeBetaCubicGradient_terminal_identity p r (p*b) t (0 : Plane)
    have hz : planeOfPair (0,0)=0 := by ext i; fin_cases i <;> rfl
    simpa [planarValueCoordinateDerivative,pairOfPlane,hz] using he
  have hv := planeRFCFSteps_coordinates_zero p r hp hr _ hh
  rw [hg] at hv
  change p^2 • planeTerminalRho r t+Q _=0 at hv
  have hmodel : ContinuousLinearMap.id ℝ Plane+p • planeRFCFModelOperator r t+(p*b) • planeLastProjection=Q := by
    dsimp only [Q,W]
    module
  have hcorr : combine (planeRFCFSteps p r)
      (modelCoefficients (planeRFCFSteps p r) (correctionCompression (planeRFCFSteps p r) Q)
        (p^2 • planeTerminalRho r t))=planeBetaRFCFCorrection p r (p*b) t := by
    unfold planeBetaRFCFCorrection
    rw [planeBetaRFCF_observed_model p r (p*b) hp hr hβ t,hg,hmodel]
  rw [hcorr] at hv
  simpa only [Q,W,_root_.add_apply,_root_.smul_apply,ContinuousLinearMap.id_apply,neg_smul] using
    eq_neg_of_add_eq_zero_right hv

end
end krylov.Functions
