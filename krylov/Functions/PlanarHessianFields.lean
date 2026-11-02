import krylov.Functions.PlanarScaledFamily
import krylov.Functions.CubicSelfConcordant

/-!
Article: main_krylov, prop:Fcycle(iii), genuine planar Hessian normalization.
Use: identify the real Riesz-gradient derivative and constant third variation
of the full indistinguishable scalar cubic, including its prescribed varying
quadratic perturbation. Source: the actual polynomial derivative rules.
-/
namespace krylov.Functions
noncomputable section
open Set Metric krylov.Tensor.BinaryCubic
open scoped InnerProductSpace

/-- The genuine affine perturbation of the scalar cubic's Euclidean Hessian.
Article: main_krylov, prop:Fcycle(iii). -/
def planeValueHessianOperator (p r : ℝ) (t : krylov.Tensor.BinaryCubic) (x : Plane) : Plane →L[ℝ] Plane :=
  (EuclideanSpace.proj 0).smulRight
    (planeOfPair (t.t0*x 0+t.t1*x 1-t.t0*p/2,t.t1*x 0+t.t2*x 1-t.t1*p/2))+
  (EuclideanSpace.proj 1).smulRight
    (planeOfPair (t.t1*x 0+t.t2*x 1-t.t1*p/2,t.t2*x 0+t.t3*x 1-t.t2*p-t.t3*r*p/2))

/-- The true full Euclidean Hessian of the actual scalar cubic.
Article: main_krylov, prop:Fcycle(iii). -/
def planeCubicHessian (p r : ℝ) (t : krylov.Tensor.BinaryCubic) (x : Plane) : Plane →L[ℝ] Plane :=
  ContinuousLinearMap.id ℝ Plane+planeValueHessianOperator p r t x

set_option maxHeartbeats 800000 in
/-- Differentiating the actual mathematical gradient gives the displayed
true Hessian field. Article: main_krylov, prop:Fcycle(iii). -/
theorem planeCubicGradient_hasFDerivAt (p r : ℝ) (t : krylov.Tensor.BinaryCubic) (x : Plane) :
    HasFDerivAt (gradient (planeCubicObjective p r t)) (planeCubicHessian p r t x) x := by
  let φ := EuclideanSpace.proj (𝕜:=ℝ) (ι:=Fin 2) 0
  let ψ := EuclideanSpace.proj (𝕜:=ℝ) (ι:=Fin 2) 1
  have hφ := φ.hasFDerivAt (x:=x)
  have hψ := ψ.hasFDerivAt (x:=x)
  have hA := (((((hφ.pow 2).const_mul (t.t0/2)).add ((hφ.mul hψ).const_mul t.t1)).add
    ((hψ.pow 2).const_mul (t.t2/2))).sub (hφ.const_mul (t.t0*p/2))).sub (hψ.const_mul (t.t1*p/2))
  have hB := ((((((hφ.pow 2).const_mul (t.t1/2)).add ((hφ.mul hψ).const_mul t.t2)).add
    ((hψ.pow 2).const_mul (t.t3/2))).sub (hφ.const_mul (t.t1*p/2))).sub
    (hψ.const_mul (t.t2*p))).sub (hψ.const_mul (t.t3*r*p/2))
  have hh := ((hasFDerivAt_id x).sub_const (planeOfPair (p,r*p))).add
    ((hA.smul_const (planeOfPair (1,0))).add (hB.smul_const (planeOfPair (0,1))))
  convert! hh using 1
  · funext y
    rw [planeCubicGradient_actual]
    ext i
    fin_cases i <;>
      simp [planeCubicGradient,planarCubicGradient,planarValueCoordinateDerivative,
        planeOfPair,pairOfPlane,φ,ψ] <;> ring
  · apply ContinuousLinearMap.ext
    intro v
    ext i
    fin_cases i <;>
      simp [planeCubicHessian,planeValueHessianOperator,planeOfPair,φ,ψ,
        ContinuousLinearMap.smulRight_apply] <;> ring

/-- The actual Hessian is its true terminal matrix plus the constant cubic
third variation on the displacement from the last observed point.
Article: main_krylov, prop:Fcycle(iii), true-minimizer metric perturbation. -/
theorem planeCubicHessian_terminal_identity (p r : ℝ) (t : krylov.Tensor.BinaryCubic) (x : Plane) :
    planeCubicHessian p r t x=ContinuousLinearMap.id ℝ Plane+p • planeTerminalOperator r t+
      canonicalVariation t.tensor (x-planeOfPair (p,r*p)) := by
  apply ContinuousLinearMap.ext
  intro v
  apply ext_inner_left ℝ
  intro w
  rw [add_apply,inner_add_right,canonicalVariation_pair]
  simp [planeCubicHessian,planeValueHessianOperator,planeTerminalOperator,planeOfPair,
    PiLp.inner_apply,Fin.sum_univ_two,tensor_apply,
    ContinuousLinearMap.smulRight_apply]
  ring

/-- The genuine Hessian differentiates to the actual constant cubic third
variation, including all prescribed quadratic and linear terms.
Article: main_krylov, prop:Fcycle(iii). -/
theorem planeCubicHessian_hasFDerivAt (p r : ℝ) (t : krylov.Tensor.BinaryCubic) (x : Plane) :
    HasFDerivAt (planeCubicHessian p r t) (canonicalVariation t.tensor) x := by
  let S := canonicalVariation t.tensor
  let A := ContinuousLinearMap.id ℝ Plane+p • planeTerminalOperator r t-S (planeOfPair (p,r*p))
  have he : planeCubicHessian p r t=fun y=>A+S y := by
    funext y
    rw [planeCubicHessian_terminal_identity,map_sub]
    dsimp only [A]
    abel
  rw [he]
  exact (S.hasFDerivAt (𝕜:=ℝ) (F:=Plane →L[ℝ] Plane) (x:=x)).const_add A

end
end krylov.Functions
