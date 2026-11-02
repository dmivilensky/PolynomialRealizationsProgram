import krylov.Nonlinear.AveragedComparison

/-!
Article: main_krylov, thm:RFCS, actual metric-coordinate derivative transport.
Use: Transport real averaged derivatives, gradient-model maps and their
actual first derivatives to the canonical self-adjoint metric coordinates
without changing the original physical algorithm. The algebraic identities
hold for every continuous linear coordinate equivalence; in the actual
Hessian/gradient application the inverse coordinate map is self-adjoint.
Source: exact Bochner integral/continuous-linear-map commutation and the
ordinary Fréchet chain rule in mathlib.
-/

namespace krylov.Nonlinear
noncomputable section
open Set chebyshev1.Nonlinear
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The actual inverse congruence of a derivative field in continuous linear metric coordinates.
Use: Express the canonical Hessian when the inverse metric coordinate map is self-adjoint.
Article: main_krylov, thm:RFCS, actual canonical derivative and averaged-Hessian transport.
-/
def coordinateDerivative (T : E ≃L[ℝ] E) (H : E → E →L[ℝ] E) (y : E) : E →L[ℝ] E :=
  T.symm.toContinuousLinearMap.comp ((H (T.symm y)).comp T.symm.toContinuousLinearMap)

/-- The genuine average of an inverse-congruence derivative field is exactly the inverse-congruence action of the original true segment average.
Use: Apply sharp canonical segment comparisons to the actual physical probe/full-step Hessians.
Article: main_krylov, thm:RFCS, actual canonical derivative and averaged-Hessian transport.
Proof: Transport the real affine segment by the exact inverse coordinate map, commute that continuous linear map with the genuine Bochner integral and use the proved integral evaluation identity.
-/
theorem averagedDerivative_coordinate_apply (T : E ≃L[ℝ] E) (H : E → E →L[ℝ] E) (x u v : E)
    (hH : ContinuousOn (fun t : ℝ => H (x+t • u)) (Icc 0 1)) :
    averagedDerivative (coordinateDerivative T H) (T x) (T u) v=
      T.symm (averagedDerivative H x u (T.symm v)) := by
  have he (t : ℝ) : coordinateDerivative T H (T x+t • T u)=
      T.symm.toContinuousLinearMap.comp ((H (x+t • u)).comp T.symm.toContinuousLinearMap) := by
    simp only [coordinateDerivative,map_add,map_smul,T.symm_apply_apply]
  have hc : ContinuousOn (fun t : ℝ => coordinateDerivative T H (T x+t • T u)) (Icc 0 1) := by
    simp only [he]
    exact continuousOn_const.clm_comp (hH.clm_comp continuousOn_const)
  have hi := hH.intervalIntegrable_of_Icc (μ := MeasureTheory.volume) (by norm_num : (0 : ℝ)≤1)
  have hi' := hc.intervalIntegrable_of_Icc (μ := MeasureTheory.volume) (by norm_num : (0 : ℝ)≤1)
  rw [averagedDerivative,ContinuousLinearMap.intervalIntegral_apply hi']
  simp only [he,ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe]
  have hiv : IntervalIntegrable (fun t : ℝ => H (x+t • u) (T.symm v)) MeasureTheory.volume 0 1 :=
    (hH.clm_apply continuousOn_const).intervalIntegrable_of_Icc (μ := MeasureTheory.volume)
    (by norm_num : (0 : ℝ)≤1)
  change (∫ t in (0 : ℝ)..1, T.symm.toContinuousLinearMap (H (x+t • u) (T.symm v)))=
    T.symm.toContinuousLinearMap (averagedDerivative H x u (T.symm v))
  rw [T.symm.toContinuousLinearMap.intervalIntegral_comp_comm hiv]
  congr 1
  exact (ContinuousLinearMap.intervalIntegral_apply hi (T.symm v)).symm


/-- The inverse-coordinate congruence of a genuine gradient-model map.
Use: Use the actual canonical gradient for the self-adjoint metric coordinate equivalence.
Article: main_krylov, thm:RFCS, actual canonical derivative and averaged-Hessian transport.
-/
def coordinateGradient (T : E ≃L[ℝ] E) (G : E → E) (y : E) : E := T.symm (G (T.symm y))

/-- The genuine continuous linear operator sending a derivative to its inverse coordinate congruence.
Use: Differentiate the true canonically normalized Hessian field by the ordinary chain rule.
Article: main_krylov, thm:RFCS, actual canonical derivative and averaged-Hessian transport.
-/
def coordinateCongruence (T : E ≃L[ℝ] E) : (E →L[ℝ] E) →L[ℝ] E →L[ℝ] E :=
  (ContinuousLinearMap.compL ℝ E E E T.symm.toContinuousLinearMap).comp
    ((ContinuousLinearMap.compL ℝ E E E).flip T.symm.toContinuousLinearMap)

/-- The genuine segment-averaged operator in metric coordinates is exactly the true inverse congruence of the original physical segment average.
Use: Compare actual nonlinear full-step and finite-probe Hessians in the original canonical error norm.
Article: main_krylov, thm:RFCS, exact actual averaged-Hessian congruence.
Proof: Read every actual operator action from the proved genuine Bochner-integral coordinate identity.
-/
theorem averagedDerivative_coordinate_operator (T : E ≃L[ℝ] E) (H : E → E →L[ℝ] E) (x u : E)
    (hH : ContinuousOn (fun t : ℝ => H (x+t • u)) (Set.Icc 0 1)) :
    averagedDerivative (coordinateDerivative T H) (T x) (T u)=coordinateCongruence T (averagedDerivative H x u) := by
  apply ContinuousLinearMap.ext
  intro v
  rw [averagedDerivative_coordinate_apply T H x u v hH]
  rfl

/-- The inverse-coordinate transport of the genuine derivative of the physical Hessian field.
Use: Keep the true self-concordance differential inequality tied to actual canonical Hessian derivatives.
Article: main_krylov, thm:RFCS, actual canonical derivative and averaged-Hessian transport.
-/
def coordinateHessianVariation (T : E ≃L[ℝ] E) (D : E → E →L[ℝ] E →L[ℝ] E) (y : E) :
    E →L[ℝ] E →L[ℝ] E :=
  (coordinateCongruence T).comp ((D (T.symm y)).comp T.symm.toContinuousLinearMap)

omit [CompleteSpace E] in
/-- The actual derivative of the inverse-coordinate gradient-model map is the genuine inverse-congruence derivative field.
Use: Derive canonical gradient/Hessian consistency from the original physical function data.
Article: main_krylov, thm:RFCS, actual canonical derivative and averaged-Hessian transport.
Proof: Apply the real Fréchet chain rule to the two true linear coordinate maps and the original genuine derivative.
-/
theorem coordinateGradient_hasFDerivAt (T : E ≃L[ℝ] E) (G : E → E) (H : E → E →L[ℝ] E)
    (y : E) (hG : HasFDerivAt G (H (T.symm y)) (T.symm y)) :
    HasFDerivAt (coordinateGradient T G) (coordinateDerivative T H y) y := by
  exact T.symm.toContinuousLinearMap.hasFDerivAt.comp y
    (hG.comp y T.symm.toContinuousLinearMap.hasFDerivAt)

omit [CompleteSpace E] in
/-- The actual derivative of the inverse-congruence derivative field is precisely its genuine transported Hessian variation.
Use: Derive canonical self-concordant Hessian differential data without an assumed transformed derivative.
Article: main_krylov, thm:RFCS, actual canonical derivative and averaged-Hessian transport.
Proof: Compose the true original Hessian derivative with the actual inverse coordinate map and continuous linear congruence operator.
-/
theorem coordinateDerivative_hasFDerivAt (T : E ≃L[ℝ] E) (H : E → E →L[ℝ] E)
    (D : E → E →L[ℝ] E →L[ℝ] E) (y : E) (hH : HasFDerivAt H (D (T.symm y)) (T.symm y)) :
    HasFDerivAt (coordinateDerivative T H) (coordinateHessianVariation T D y) y := by
  exact (coordinateCongruence T).hasFDerivAt.comp y (hH.comp y T.symm.toContinuousLinearMap.hasFDerivAt)

end
end krylov.Nonlinear
