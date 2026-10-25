import polyak.CertifiedExamples.Exact313.LiteralProfile
import polyak.CertifiedExamples.Exact313.ChartJacobian
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

/-! Nonsingularity of the actual three lag-contact equations, including
 their original `(κ,y,β)` coordinates. -/
noncomputable section
namespace polyak.CertifiedExamples.Exact313
open General Levels Set LeanCert.Engine

private theorem invertible_of_injective (D : CoefficientVector→L[ℝ]CoefficientVector)
    (hi : Function.Injective D) : D.IsInvertible := by
  have hs : Function.Surjective D :=
    (LinearMap.injective_iff_surjective (f:=D.toLinearMap)).mp hi
  refine ⟨(LinearEquiv.ofBijective D.toLinearMap ⟨hi,hs⟩).toContinuousLinearEquiv,?_⟩
  ext x i
  rfl

theorem radialFactor_negative (z : CoefficientVector) {x : ℝ} (hx : x∈Ioo 0 Real.pi) :
    radialFactor z x<0 := by
  have hc : Real.cos x<1 := by
    have h := Real.cos_lt_cos_of_nonneg_of_le_pi (by norm_num : (0:ℝ)≤0) hx.2.le hx.1
    simpa using h
  have hu : c₁<1 := c₁_mem.2
  exact mul_neg_of_neg_of_pos
    (div_neg_of_neg_of_pos (neg_neg_of_pos (sub_pos.mpr hu)) (sourceRadius_positive z u_interior))
    (div_pos (sub_pos.mpr hc) (sourceRadius_positive z hx))

theorem literalMatrix_det_ne_zero (z : CoefficientVector) : (literalMatrix z).det≠0 := by
  have hu := (radialFactor_negative z u_interior).ne
  have hv := (radialFactor_negative z v_interior).ne
  have hsu := (Real.sin_pos_of_pos_of_lt_pi u_interior.1 u_interior.2).ne'
  have hsv := (Real.sin_pos_of_pos_of_lt_pi v_interior.1 v_interior.2).ne'
  unfold literalMatrix
  rw [Matrix.det_fin_three]
  norm_num
  exact ⟨⟨hv,hu,hsu⟩,hv,hsv⟩

theorem literalMatrix_invertible (z : CoefficientVector) : (matrixCLM (literalMatrix z)).IsInvertible := by
  apply invertible_of_injective
  exact Matrix.mulVec_injective_of_isUnit
    ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr (literalMatrix_det_ne_zero z)))

theorem literalContactSystem_zero_iff (z : CoefficientVector) :
    literalContactSystem z=0 ↔ contactSystem z=0 := by
  rw [literalContactSystem_eq]
  have hi := Matrix.mulVec_injective_of_isUnit
    ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr (literalMatrix_det_ne_zero z)))
  constructor
  · intro h
    apply hi
    simpa using h
  · intro h
    simp [h]

theorem sourceRadius_parameter_differentiableAt (z : CoefficientVector) {x : ℝ}
    (hx : x∈Ioo 0 Real.pi) : DifferentiableAt ℝ (fun z=>sourceRadius z x) z := by
  have h : DifferentiableAt ℝ (fun z:CoefficientVector=>vectorXi z (Real.cos x)^2+Real.sin x^2) z := by
    dsimp [vectorXi]
    fun_prop
  exact h.sqrt (radius_argument_positive z hx).ne'

theorem radialFactor_parameter_differentiableAt (z : CoefficientVector) {x : ℝ}
    (hx : x∈Ioo 0 Real.pi) : DifferentiableAt ℝ (fun z=>radialFactor z x) z := by
  unfold radialFactor
  simp only [div_eq_mul_inv]
  exact ((differentiableAt_const _).mul ((sourceRadius_parameter_differentiableAt z u_interior).inv
      (sourceRadius_positive z u_interior).ne')).mul
    ((differentiableAt_const _).mul ((sourceRadius_parameter_differentiableAt z hx).inv
      (sourceRadius_positive z hx).ne'))

theorem radiusSlope_parameter_differentiableAt (z : CoefficientVector) {x : ℝ}
    (hx : x∈Ioo 0 Real.pi) : DifferentiableAt ℝ (fun z=>radiusSlope z x) z := by
  have hn : DifferentiableAt ℝ (fun z:CoefficientVector=>
      vectorXi z (Real.cos x)*vectorXiD z (Real.cos x)*(-Real.sin x)+Real.sin x*Real.cos x) z := by
    unfold vectorXi vectorXiD
    fun_prop
  exact hn.mul ((sourceRadius_parameter_differentiableAt z hx).inv
    (sourceRadius_positive z hx).ne')

theorem radialFactorSlope_parameter_differentiableAt (z : CoefficientVector) {x : ℝ}
    (hx : x∈Ioo 0 Real.pi) : DifferentiableAt ℝ (fun z=>radialFactorSlope z x) z := by
  have hR := sourceRadius_parameter_differentiableAt z hx
  have hRu := sourceRadius_parameter_differentiableAt z u_interior
  have hD := radiusSlope_parameter_differentiableAt z hx
  unfold radialFactorSlope
  simp only [div_eq_mul_inv]
  exact ((differentiableAt_const _).mul (hRu.inv (sourceRadius_positive z u_interior).ne')).mul
    ((((differentiableAt_const _).mul hR).sub ((differentiableAt_const _).mul hD)).mul
      ((hR.pow 2).inv (pow_ne_zero _ (sourceRadius_positive z hx).ne')))

private def matrixAssemblyLinear : (Fin 3→Fin 3→ℝ)→ₗ[ℝ]
    (CoefficientVector→L[ℝ]CoefficientVector) where
  toFun := matrixCLM
  map_add' A B := by
    ext z i
    change Matrix.mulVec (A+B) z i=Matrix.mulVec A z i+Matrix.mulVec B z i
    exact congrFun (Matrix.add_mulVec A B z) i
  map_smul' c A := by
    ext z i
    change Matrix.mulVec (c • A) z i=c*(Matrix.mulVec A z i)
    exact congrFun (Matrix.smul_mulVec c A z) i

private def matrixAssembly : (Fin 3→Fin 3→ℝ)→L[ℝ]
    (CoefficientVector→L[ℝ]CoefficientVector) :=
  matrixAssemblyLinear.toContinuousLinearMap

private theorem matrixAssembly_apply (A : Fin 3→Fin 3→ℝ) : matrixAssembly A=matrixCLM A := by
  ext x i
  rfl

theorem literalMatrix_differentiableAt (z : CoefficientVector) :
    DifferentiableAt ℝ (fun z i j=>literalMatrix z i j) z := by
  apply differentiableAt_pi.mpr
  intro i
  apply differentiableAt_pi.mpr
  intro j
  fin_cases i <;> fin_cases j
  · exact radialFactor_parameter_differentiableAt z v_interior
  · exact differentiableAt_const _
  · exact differentiableAt_const _
  · exact differentiableAt_const _
  · exact (radialFactor_parameter_differentiableAt z u_interior).mul_const _
  · exact differentiableAt_const _
  · exact radialFactorSlope_parameter_differentiableAt z v_interior
  · exact differentiableAt_const _
  · exact (radialFactor_parameter_differentiableAt z v_interior).mul_const _

theorem contactSystem_differentiableAt (z : CoefficientVector) :
    DifferentiableAt ℝ contactSystem z := by
  have hXi (c : ℝ) : DifferentiableAt ℝ (fun z:CoefficientVector=>vectorXi z c) z := by
    unfold vectorXi
    fun_prop
  have hXiD (c : ℝ) : DifferentiableAt ℝ (fun z:CoefficientVector=>vectorXiD z c) z := by
    unfold vectorXiD
    fun_prop
  have hN : DifferentiableAt ℝ ratioNumerator z := (differentiableAt_const _).sub (hXi c₁)
  have hD : DifferentiableAt ℝ ratioDenominator z := ((hXi c₁).mul_const _).add_const _
  have hP (c : ℝ) : DifferentiableAt ℝ (fun z=>contactProfile z c) z :=
    (hD.mul ((hXi c).sub_const _)).add (hN.mul (((hXi c).mul_const _).add_const _))
  have hS (c : ℝ) : DifferentiableAt ℝ (fun z=>profileSlope z c) z :=
    (hD.mul ((hXiD c).sub_const _)).add
      (hN.mul (((((hXiD c).mul_const _).add ((hXi c).mul_const _)).add_const _).add_const _))
  apply differentiableAt_pi.mpr
  intro i
  fin_cases i
  · exact hP c₂
  · exact hS c₁
  · exact hS c₂

theorem literalContactSystem_differentiableAt (z : CoefficientVector) :
    DifferentiableAt ℝ literalContactSystem z := by
  have hm := matrixAssembly.differentiableAt.comp z (literalMatrix_differentiableAt z)
  have h := hm.clm_apply (contactSystem_differentiableAt z)
  have he : (fun z=>matrixAssembly (literalMatrix z) (contactSystem z))=literalContactSystem := by
    funext y
    exact (literalContactSystem_eq y).symm
  change DifferentiableAt ℝ (fun y=>matrixAssembly (literalMatrix y) (contactSystem y)) z at h
  rwa [he] at h

theorem literalContactSystem_fderiv :
    fderiv ℝ literalContactSystem coefficientVector=
      (matrixCLM (literalMatrix coefficientVector)).comp
        (fderiv ℝ contactSystem coefficientVector) := by
  have hm := matrixAssembly.differentiableAt.comp coefficientVector
    (literalMatrix_differentiableAt coefficientVector)
  have h := hm.hasFDerivAt.clm_apply (contactSystem_differentiableAt coefficientVector).hasFDerivAt
  have he : (fun z=>matrixAssembly (literalMatrix z) (contactSystem z))=literalContactSystem := by
    funext y
    exact (literalContactSystem_eq y).symm
  change HasFDerivAt (fun y=>matrixAssembly (literalMatrix y) (contactSystem y)) _ coefficientVector at h
  rw [he,contactSystem_zero] at h
  simpa only [Function.comp_apply,matrixAssembly_apply,map_zero,add_zero] using h.fderiv

theorem literalContactSystem_jacobian_invertible :
    (fderiv ℝ literalContactSystem coefficientVector).IsInvertible := by
  rw [literalContactSystem_fderiv]
  exact (literalMatrix_invertible coefficientVector).comp contactSystem_jacobian_invertible

def originalContactSystem (p : ChartJacobian.E) : ChartJacobian.E :=
  literalContactSystem (ChartJacobian.coefficientMap p)

theorem coefficientMap_qStar : ChartJacobian.coefficientMap (ChartJacobian.originalPoint qStar)=coefficientVector := by
  rw [ChartJacobian.coefficientMap_actual,qStar_coefficients]
  rfl

theorem originalContactSystem_zero : originalContactSystem (ChartJacobian.originalPoint qStar)=0 := by
  unfold originalContactSystem
  rw [coefficientMap_qStar,literalContactSystem_zero_iff]
  exact contactSystem_zero

theorem originalContactSystem_jacobian_invertible :
    (fderiv ℝ originalContactSystem (ChartJacobian.originalPoint qStar)).IsInvertible := by
  have hβ : 1-qStar.beta≠0 := (sub_pos.mpr qStar.beta_lt_one).ne'
  have hn := (ChartJacobian.analyticAt_normalization (ChartJacobian.originalPoint qStar)
    qStar.kappa_pos.ne' hβ).differentiableAt
  have hb : (ChartJacobian.normalization (ChartJacobian.originalPoint qStar)) 1≠0 :=
    (div_pos qStar.B_pos (sub_pos.mpr qStar.beta_lt_one)).ne'
  have hc := (ChartJacobian.normalizedCoefficients_differentiableAt hb).comp
    (ChartJacobian.originalPoint qStar) hn
  have he := fderiv_comp (ChartJacobian.originalPoint qStar)
    (literalContactSystem_differentiableAt (ChartJacobian.coefficientMap (ChartJacobian.originalPoint qStar))) hc
  change fderiv ℝ originalContactSystem (ChartJacobian.originalPoint qStar)=_ at he
  rw [he,coefficientMap_qStar]
  exact literalContactSystem_jacobian_invertible.comp (ChartJacobian.coefficientMap_jacobian_invertible qStar)

end polyak.CertifiedExamples.Exact313
