import krylov.Functions.PlanarRFCFOriginalScale
import krylov.Functions.SegmentHessian

/-!
Article: main_krylov, thm:Fplanar, the literal original first average A0.
Use: identify the genuine Bochner average of the actual scalar Riesz-gradient
Hessian with I+beta*h*hᵀ, for every independent beta and actual cubic.
Source: genuine derivative uniqueness and the exact affine-Hessian integral.
-/
namespace krylov.Functions
noncomputable section
open krylov.Tensor.BinaryCubic chebyshev1.Nonlinear
open scoped InnerProductSpace

/-- The original independent unknown base is exactly the true averaged
first-segment Hessian of the genuine scalar objective. No midpoint or
operator-field convention is substituted for the actual mathematical
second derivative. Article: main_krylov, thm:Fplanar, A0=I+beta*h*hᵀ. -/
theorem planeUnknownBase_first_average (p r β : ℝ) (t : krylov.Tensor.BinaryCubic) :
    averagedDerivative (fderiv ℝ (gradient (planeUnknownBaseObjective p r β t)))
      (0 : Plane) (planeOfPair (p,0))=
      ContinuousLinearMap.id ℝ Plane+β • planeLastProjection := by
  let b := β+p*(t.t2+r*t.t3)/2
  let H := fun x : Plane=>planeCubicHessian p r t x+b • planeLastProjection
  let T := canonicalVariation t.tensor
  have hd : fderiv ℝ (gradient (planeUnknownBaseObjective p r β t))=H := by
    funext x
    exact (planeBetaCubicGradient_hasFDerivAt p r b t x).fderiv
  have he : H=fun x=>H 0+T x := by
    funext x
    dsimp only [H,T]
    simp only [planeCubicHessian_terminal_identity,map_sub,zero_sub,map_neg]
    abel
  have havg : averagedDerivative H (0 : Plane) (planeOfPair (p,0))=
      H ((1/2 : ℝ) • planeOfPair (p,0)) := by
    conv_lhs => rw [he,averagedHessian_affine]
    simpa only [zero_add] using (congrFun he ((1/2 : ℝ) • planeOfPair (p,0))).symm
  have hmid : (1/2 : ℝ) • planeOfPair (p,0)=planeOfPair (p/2,0) := by
    ext i
    fin_cases i <;> simp [planeOfPair]; ring
  rw [hd,havg,hmid]
  exact (planeBetaCubicGradient_hasFDerivAt p r b t (planeOfPair (p/2,0))).unique
    (planeUnknownBase_first_hessian p r β t)

end
end krylov.Functions
