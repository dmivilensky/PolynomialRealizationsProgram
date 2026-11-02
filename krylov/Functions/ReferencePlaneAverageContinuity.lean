import krylov.Functions.ReferencePlaneFullReference
import krylov.Functions.SegmentHessian

/-!
Article: main_krylov, s7:N and prop:Fcycle(iii), actual source continuity.
Use: identify the genuine first average with the true affine Hessian at its
midpoint before taking a compact family of actual normalized references.
Source: actual constant third derivative and exact Bochner midpoint average.
-/
namespace krylov.Functions
noncomputable section
open krylov.Reference krylov.Nonlinear krylov.Tensor.BinaryCubic chebyshev1.Nonlinear
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {n : ℕ}

/-- The genuine affine full Hessian has exactly its midpoint segment average.
Article: main_krylov, prop:Fcycle(iii), actual observed source matrix. -/
theorem hilbertPlaneHessian_averaged (e h : E) (p r : ℝ) (t : krylov.Tensor.BinaryCubic) (a s : E) :
    averagedDerivative (hilbertPlaneHessian e h p r t) a s=
      hilbertPlaneHessian e h p r t (a+(1/2 : ℝ) • s) := by
  have he : hilbertPlaneHessian e h p r t=fun x=>hilbertPlaneHessian e h p r t 0+hilbertPlaneVariation e h t x := by
    funext x
    have hs := hilbertPlaneHessian_sub e h p r t x 0
    rw [sub_zero] at hs
    change hilbertPlaneHessian e h p r t x-hilbertPlaneHessian e h p r t 0=hilbertPlaneVariation e h t x at hs
    exact sub_eq_iff_eq_add.mp hs |>.trans (add_comm _ _)
  conv_lhs => rw [he,averagedHessian_affine]
  exact congrFun he (a+(1/2 : ℝ) • s) |>.symm

/-- The actual observed first operator is the true root congruence of the
actual canonical midpoint Hessian. Article: prop:Fcycle(iii), s7:N. -/
theorem referencePlaneObservedOperator_midpoint
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) (g : EuclideanSpace ℝ (Fin n))
    (ε : ℝ) (t : krylov.Tensor.BinaryCubic) :
    cgOperator (referencePlaneObservedMatrix A hA g ε t)=
      coordinateCongruence (metricCoordinates A hA).symm
        (hilbertPlaneHessian (referencePlaneFirst A g) (referencePlaneLast A hA g)
          (ε*‖canonicalCGStep A g 0‖) (referencePlaneRatio A hA g) t
          ((1/2 : ℝ) • (ε • canonicalCGStep A g 0))) := by
  rw [referencePlaneObservedMatrix,metricHilbertPlaneFirstSecant_eq,
    ←metricCongruence_physicalMatrix,physicalOperatorMatrix_operator,hilbertPlaneHessian_averaged,zero_add]

/-- The genuine observed operator is continuous in the real source scale,
real tensor amplitude and the four original binary tensor coefficients.
Article: main_krylov, s7:N, actual lower-source compact admission. -/
theorem referencePlaneObservedOperator_continuous
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) (g : EuclideanSpace ℝ (Fin n)) :
    Continuous (fun z : ℝ × ℝ × (Fin 4 → ℝ)=>
      cgOperator (referencePlaneObservedMatrix A hA g z.1 (scaleBinaryCubic z.2.1 (binaryFromVector z.2.2)))) := by
  simp only [referencePlaneObservedOperator_midpoint]
  apply (coordinateCongruence (metricCoordinates A hA).symm).continuous.comp
  unfold hilbertPlaneHessian hilbertPlaneLiftOperator planeCubicHessian planeValueHessianOperator
    scaleBinaryCubic binaryFromVector planeOfPair
  fun_prop

end
end krylov.Functions
