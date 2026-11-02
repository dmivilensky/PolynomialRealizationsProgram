import krylov.Functions.PlanarRFCFWorst
import krylov.Functions.PlanarScaledFamily
import krylov.Methods.HomogeneousSolve

/-!
Article: main_krylov, thm:Fplanar and prop:Fcycle(iii), actual RFC-F tensor shrink.
Use: retain the true observed model solve under the common tensor shrink
needed for the true-minimizer SC sources. Source: exact scalar polynomial
homogeneity and the implemented model coefficient homogeneity.
-/
namespace krylov.Functions
noncomputable section
open Set Metric Matrix krylov.Tensor.BinaryCubic krylov.Methods krylov.Correction
open scoped InnerProductSpace BigOperators Matrix.Norms.L2Operator

/-- The genuine observed normalized model scales by the original tensor scale.
Article: main_krylov, thm:Fplanar. -/
theorem planeRFCFModelOperator_scale (α r : ℝ) (t : krylov.Tensor.BinaryCubic) :
    planeRFCFModelOperator r (scaleBinaryCubic α t)=α • planeRFCFModelOperator r t := by
  apply ContinuousLinearMap.ext
  intro v
  ext i
  fin_cases i <;> simp [planeRFCFModelOperator,planeOfPair,scaleBinaryCubic,
    ContinuousLinearMap.smulRight_apply] <;> ring

/-- The actual entire value-model output commutes with true tensor shrinking.
No model invertibility or output expansion is assumed: the totalized
implemented coefficient solve obeys exact homogeneity.
Article: main_krylov, thm:Fplanar and prop:Fcycle(iii). -/
theorem planeRFCFOutput_tensor_scale (p r α : ℝ) (hp : p≠0) (hr : r≠0) (hα : α≠0)
    (t : krylov.Tensor.BinaryCubic) :
    α • planeRFCFOutput p r (scaleBinaryCubic α t)=planeRFCFOutput (α*p) r t := by
  let f := planeCubicObjective p r (scaleBinaryCubic α t)
  let g := gradient f (planeOfPair (p,r*p))
  let H := valueCorrectedModel f (fun x=>innerSL ℝ (gradient f x))
    (planeRFCFAnchors p) (planeRFCFSteps p r) (planeRFCFSplit p r (scaleBinaryCubic α t))
  have hlast : α • planeOfPair (p,r*p)=planeOfPair (α*p,r*(α*p)) := by
    ext i
    fin_cases i <;> simp [planeOfPair]; ring
  have hS : planeRFCFSteps (α*p) r=fun i=>α • planeRFCFSteps p r i := by
    funext i
    fin_cases i <;> ext j <;> fin_cases j <;> simp [planeRFCFSteps,planeOfPair]; ring
  have hQ : ContinuousLinearMap.id ℝ Plane+(α*p) • planeRFCFModelOperator r t=
      ContinuousLinearMap.id ℝ Plane+p • planeRFCFModelOperator r (scaleBinaryCubic α t) := by
    rw [planeRFCFModelOperator_scale,smul_smul,show p*α=α*p by ring]
  have hmodel : valueCorrectedModel (planeCubicObjective (α*p) r t)
      (fun x=>innerSL ℝ (gradient (planeCubicObjective (α*p) r t) x))
      (planeRFCFAnchors (α*p)) (planeRFCFSteps (α*p) r) (planeRFCFSplit (α*p) r t)=
      (α*α) • H := by
    rw [planeRFCF_observed_model (α*p) r (mul_ne_zero hα hp) hr t]
    dsimp only [H,f]
    rw [planeRFCF_observed_model p r hp hr (scaleBinaryCubic α t),hS,hQ]
    ext i j
    simp only [correctionCompression,crossGram,map_smul,real_inner_smul_left,
      real_inner_smul_right,Matrix.smul_apply,smul_eq_mul]
    ring
  have hg : gradient (planeCubicObjective (α*p) r t) (planeOfPair (α*p,r*(α*p)))=α • g := by
    have hh := planeCubicGradient_tensor_scale p r α hα t (planeOfPair (p,r*p))
    rw [hlast] at hh
    dsimp only [g,f]
    rw [hh,smul_smul,mul_inv_cancel₀ hα,one_smul]
  unfold planeRFCFOutput planeRFCFCorrection
  rw [hmodel,hS,hg,modelCoefficients_scalar _ H g α hα,combine_scalar,←hlast,smul_add]

/-- The actual scalar-gradient norm obeys exact positive tensor homogeneity.
Article: main_krylov, thm:Fplanar, true SC shrink transfer. -/
theorem planeRFCFOutput_gradient_tensor_scale (p r α : ℝ) (hp : p≠0) (hr : r≠0)
    (hα : 0<α) (t : krylov.Tensor.BinaryCubic) :
    ‖gradient (planeCubicObjective p r (scaleBinaryCubic α t))
        (planeRFCFOutput p r (scaleBinaryCubic α t))‖=
      α⁻¹*‖gradient (planeCubicObjective (α*p) r t) (planeRFCFOutput (α*p) r t)‖ := by
  rw [planeCubicGradient_tensor_scale p r α hα.ne',planeRFCFOutput_tensor_scale p r α hp hr hα.ne',
    norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hα.le)]

/-- Positive tensor shrinking retains the genuine sharp RFC-F norm formula
with its exact squared leading amplitude and cubic remainder amplitude.
Article: main_krylov, thm:Fplanar, true SC shrink transfer. -/
theorem planeRFCFOutput_scaled_norm_remainder (r : ℝ) (hr : r≠0) :
    ∃ ε₀ C : ℝ, 0<ε₀ ∧ 0<C ∧ ∀ p α : ℝ, 0<p → 0<α → α*p<ε₀ →
      ∀ t : krylov.Tensor.BinaryCubic, t.InBall →
      |‖gradient (planeCubicObjective p r (scaleBinaryCubic α t))
          (planeRFCFOutput p r (scaleBinaryCubic α t))‖-
        α^2*(r^2/4*rfcObjective r t)*p^3|≤C*α^3*p^4 := by
  obtain ⟨ep,C,hep,hC,hrem⟩ := planeRFCFOutput_norm_remainder r hr
  refine ⟨ep,C,hep,hC,?_⟩
  intro p α hp hα he t ht
  have heq : ‖gradient (planeCubicObjective p r (scaleBinaryCubic α t))
        (planeRFCFOutput p r (scaleBinaryCubic α t))‖-α^2*(r^2/4*rfcObjective r t)*p^3=
      α⁻¹*(‖gradient (planeCubicObjective (α*p) r t) (planeRFCFOutput (α*p) r t)‖-
        (r^2/4*rfcObjective r t)*(α*p)^3) := by
    rw [planeRFCFOutput_gradient_tensor_scale p r α hp.ne' hr hα t]
    field_simp
  rw [heq,abs_mul,abs_of_pos (inv_pos.mpr hα)]
  exact (mul_le_mul_of_nonneg_left (hrem (α*p) (mul_pos hα hp) he t ht) (inv_nonneg.mpr hα.le)).trans_eq
    (by field_simp)

end
end krylov.Functions
