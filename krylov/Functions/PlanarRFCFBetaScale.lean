import krylov.Functions.PlanarRFCFUnknownBase
import krylov.Functions.PlanarRFCFScale

/-!
Article: main_krylov, thm:Fplanar, the original tensor budget amplitude.
Use: transport the true observed independent-base solve under exact positive
cubic homogeneity, retaining the original beta rather than correlating it
with the tensor. Source: actual model compression, scalar gradient scaling
and the implemented coefficient-solve homogeneity.
-/
namespace krylov.Functions
noncomputable section
open Set Metric Matrix krylov.Tensor.BinaryCubic krylov.Methods krylov.Correction
open scoped InnerProductSpace BigOperators Matrix.Norms.L2Operator

/-- The true independent-base gradient has exact cubic scaling.
Article: main_krylov, thm:Fplanar. -/
theorem planeBetaCubicGradient_tensor_scale (p r β α : ℝ) (hα : α≠0)
    (t : krylov.Tensor.BinaryCubic) (x : Plane) :
    gradient (planeBetaCubicObjective p r β (scaleBinaryCubic α t)) x=
      α⁻¹ • gradient (planeBetaCubicObjective (α*p) r β t) (α • x) := by
  rw [planeBetaCubicGradient_actual,planeBetaCubicGradient_actual,planeCubicGradient_tensor_scale p r α hα]
  ext i
  fin_cases i <;> simp [planeOfPair,smul_add,smul_smul]
  field_simp

/-- The entire actual independent-base observed solve obeys exact tensor
homogeneity. The implemented matrix inverse remains the actual inverse;
no correction formula or expansion is postulated.
Article: main_krylov, thm:Fplanar. -/
theorem planeBetaRFCFOutput_tensor_scale (p r β α : ℝ)
    (hp : p≠0) (hr : r≠0) (hα : α≠0) (hβ : 1+β≠0) (t : krylov.Tensor.BinaryCubic) :
    α • planeBetaRFCFOutput p r β (scaleBinaryCubic α t)=planeBetaRFCFOutput (α*p) r β t := by
  let f := planeBetaCubicObjective p r β (scaleBinaryCubic α t)
  let g := gradient f (planeOfPair (p,r*p))
  let H := valueCorrectedModel f (fun x=>innerSL ℝ (gradient f x))
    (planeRFCFAnchors p) (planeRFCFSteps p r) (planeBetaRFCFSplit p r β (scaleBinaryCubic α t))
  have hlast : α • planeOfPair (p,r*p)=planeOfPair (α*p,r*(α*p)) := by
    ext i
    fin_cases i <;> simp [planeOfPair]; ring
  have hS : planeRFCFSteps (α*p) r=fun i=>α • planeRFCFSteps p r i := by
    funext i
    fin_cases i <;> ext j <;> fin_cases j <;> simp [planeRFCFSteps,planeOfPair]; ring
  have hQ : ContinuousLinearMap.id ℝ Plane+(α*p) • planeRFCFModelOperator r t+β • planeLastProjection=
      ContinuousLinearMap.id ℝ Plane+p • planeRFCFModelOperator r (scaleBinaryCubic α t)+β • planeLastProjection := by
    rw [planeRFCFModelOperator_scale,smul_smul,show p*α=α*p by ring]
  have hmodel : valueCorrectedModel (planeBetaCubicObjective (α*p) r β t)
      (fun x=>innerSL ℝ (gradient (planeBetaCubicObjective (α*p) r β t) x))
      (planeRFCFAnchors (α*p)) (planeRFCFSteps (α*p) r) (planeBetaRFCFSplit (α*p) r β t)=
      (α*α) • H := by
    rw [planeBetaRFCF_observed_model (α*p) r β (mul_ne_zero hα hp) hr hβ t]
    dsimp only [H,f]
    rw [planeBetaRFCF_observed_model p r β hp hr hβ (scaleBinaryCubic α t),hS,hQ]
    ext i j
    simp only [correctionCompression,crossGram,map_smul,real_inner_smul_left,
      real_inner_smul_right,Matrix.smul_apply,smul_eq_mul]
    ring
  have hg : gradient (planeBetaCubicObjective (α*p) r β t) (planeOfPair (α*p,r*(α*p)))=α • g := by
    have hh := planeBetaCubicGradient_tensor_scale p r β α hα t (planeOfPair (p,r*p))
    rw [hlast] at hh
    dsimp only [g,f]
    rw [hh,smul_smul,mul_inv_cancel₀ hα,one_smul]
  unfold planeBetaRFCFOutput planeBetaRFCFCorrection
  rw [hmodel,hS,hg,modelCoefficients_scalar _ H g α hα,combine_scalar,←hlast,smul_add]

/-- Original independent-base tensor homogeneity retains the exact
source parameter beta on both sides. Article: main_krylov, thm:Fplanar. -/
theorem planeUnknownBaseRFCFOutput_tensor_scale (p r β α : ℝ)
    (hp : p≠0) (hr : r≠0) (hα : α≠0) (t : krylov.Tensor.BinaryCubic)
    (hβ : 1+(β+(α*p)*(t.t2+r*t.t3)/2)≠0) :
    α • planeUnknownBaseRFCFOutput p r β (scaleBinaryCubic α t)=
      planeUnknownBaseRFCFOutput (α*p) r β t := by
  have hshift : β+p*((scaleBinaryCubic α t).t2+r*(scaleBinaryCubic α t).t3)/2=
      β+(α*p)*(t.t2+r*t.t3)/2 := by simp only [scaleBinaryCubic]; ring
  unfold planeUnknownBaseRFCFOutput
  rw [hshift]
  exact planeBetaRFCFOutput_tensor_scale p r _ α hp hr hα hβ t

/-- The true gradient norm of the original independent-base observed output
retains the exact original tensor amplitude.
Article: main_krylov, thm:Fplanar. -/
theorem planeUnknownBaseRFCFOutput_gradient_tensor_scale (p r β α : ℝ)
    (hp : p≠0) (hr : r≠0) (hα : 0<α) (t : krylov.Tensor.BinaryCubic)
    (hβ : 1+(β+(α*p)*(t.t2+r*t.t3)/2)≠0) :
    ‖gradient (planeUnknownBaseObjective p r β (scaleBinaryCubic α t))
        (planeUnknownBaseRFCFOutput p r β (scaleBinaryCubic α t))‖=
      α⁻¹*‖gradient (planeUnknownBaseObjective (α*p) r β t)
        (planeUnknownBaseRFCFOutput (α*p) r β t)‖ := by
  have hshift : β+p*((scaleBinaryCubic α t).t2+r*(scaleBinaryCubic α t).t3)/2=
      β+(α*p)*(t.t2+r*t.t3)/2 := by simp only [scaleBinaryCubic]; ring
  unfold planeUnknownBaseObjective planeUnknownBaseRFCFOutput
  rw [hshift,planeBetaCubicGradient_tensor_scale p r _ α hα.ne',
    planeBetaRFCFOutput_tensor_scale p r _ α hp hr hα.ne' hβ,
    norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hα.le)]

end
end krylov.Functions
