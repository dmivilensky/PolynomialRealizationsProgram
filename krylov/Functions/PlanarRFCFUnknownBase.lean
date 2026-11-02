import krylov.Functions.PlanarRFCFBetaWorst
import krylov.Functions.PlanarHessianFields

/-!
Article: main_krylov, thm:Fplanar, literal unknown first-secant base.
Use: express the full scalar observed-model family with the source's original
independent parameter A0=I+beta*h*hᵀ. The known tensor-dependent centering
of the earlier family is removed explicitly. Source: genuine differentiation,
the affine cubic Hessian and the already proved uniform independent-base solve.
-/
namespace krylov.Functions
noncomputable section
open Set Matrix krylov.Tensor.BinaryCubic
open scoped InnerProductSpace Matrix.Norms.L2Operator

/-- The actual scalar family parameterized by the source's independent
first-secant h-diagonal, rather than by a centered perturbation.
Article: main_krylov, thm:Fplanar, original beta. -/
def planeUnknownBaseObjective (p r β : ℝ) (t : krylov.Tensor.BinaryCubic) : Plane → ℝ :=
  planeBetaCubicObjective p r (β+p*(t.t2+r*t.t3)/2) t

/-- The genuine observed RFC-F output on the original independent-base family.
Article: main_krylov, thm:Fplanar. -/
def planeUnknownBaseRFCFOutput (p r β : ℝ) (t : krylov.Tensor.BinaryCubic) : Plane :=
  planeBetaRFCFOutput p r (β+p*(t.t2+r*t.t3)/2) t

/-- The independent-base source has its actual displayed Hessian derivative.
Article: main_krylov, thm:Fplanar. -/
theorem planeBetaCubicGradient_hasFDerivAt (p r β : ℝ) (t : krylov.Tensor.BinaryCubic) (x : Plane) :
    HasFDerivAt (gradient (planeBetaCubicObjective p r β t))
      (planeCubicHessian p r t x+β • planeLastProjection) x := by
  have hfun : gradient (planeBetaCubicObjective p r β t)=
      fun y=>gradient (planeCubicObjective p r t) y+(β*(y 1-r*p)) • planeOfPair (0,1) :=
    funext (planeBetaCubicGradient_actual p r β t)
  rw [hfun]
  have hy := ((EuclideanSpace.proj (𝕜:=ℝ) (ι:=Fin 2) 1).hasFDerivAt (x:=x)).sub_const (r*p)
  convert! (planeCubicGradient_hasFDerivAt p r t x).add
    ((hy.const_mul β).smul_const (planeOfPair (0,1))) using 1
  ext v i
  simp [planeLastProjection,planeOfPair]
  ring

set_option maxHeartbeats 800000 in
/-- The actual first-secant midpoint Hessian is exactly the original
unknown base I+beta*h*hᵀ, for every independent beta and cubic tensor.
Since the true Hessian is affine, this is also its genuine first-segment
average. Article: main_krylov, thm:Fplanar, original source dictionary. -/
theorem planeUnknownBase_first_hessian (p r β : ℝ) (t : krylov.Tensor.BinaryCubic) :
    HasFDerivAt (gradient (planeUnknownBaseObjective p r β t))
      (ContinuousLinearMap.id ℝ Plane+β • planeLastProjection) (planeOfPair (p/2,0)) := by
  have hd := planeBetaCubicGradient_hasFDerivAt p r (β+p*(t.t2+r*t.t3)/2) t (planeOfPair (p/2,0))
  convert! hd using 1
  ext v i
  fin_cases i <;> simp [planeCubicHessian,planeValueHessianOperator,planeLastProjection,
    planeOfPair,ContinuousLinearMap.smulRight_apply] <;> ring

/-- Uniform actual observed-model response on the ORIGINAL independent
unknown-base interval, after its proved exact source reparameterization.
Article: main_krylov, thm:Fplanar, all |beta|≤B*p and all true tensors. -/
theorem planeUnknownBaseRFCFOutput_norm_remainder (r B : ℝ) (hr : r≠0) (hB : 0≤B) :
    ∃ ep C : ℝ, 0<ep ∧ 0<C ∧ ∀ p β : ℝ, 0<p → p<ep → |β|≤B*p →
      ∀ t : krylov.Tensor.BinaryCubic, t.InBall →
      |‖gradient (planeUnknownBaseObjective p r β t) (planeUnknownBaseRFCFOutput p r β t)‖-
        (r^2/4*rfcObjective r t)*p^3|≤C*p^4 := by
  let B' := B+(1+|r|)/2
  have hB' : 0≤B' := by dsimp only [B']; positivity
  obtain ⟨ep,C,hep,hC,hrem⟩ := planeBetaRFCFOutput_interval_remainder r B' hr hB'
  refine ⟨ep,C,hep,hC,?_⟩
  intro p β hp he hβ t ht
  have ht2 : |t.t2|≤1 := by
    have hh := (coefficient_disks ht).2
    rw [abs_le]
    constructor <;> nlinarith only [hh,sq_nonneg t.t1]
  have ht3 := (axis_bounds ht).2
  have hsum : |t.t2+r*t.t3|≤1+|r| := by
    apply (abs_add_le _ _).trans
    rw [abs_mul]
    nlinarith only [ht2,mul_le_mul_of_nonneg_left ht3 (abs_nonneg r)]
  have hshift : |β+p*(t.t2+r*t.t3)/2|≤B'*p := by
    apply (abs_add_le _ _).trans
    rw [abs_div,abs_mul,abs_of_pos hp,show |(2:ℝ)|=2 by norm_num]
    have hh := mul_le_mul_of_nonneg_left hsum hp.le
    dsimp only [B']
    nlinarith only [hβ,hh]
  exact hrem p (β+p*(t.t2+r*t.t3)/2) hp he hshift t ht

end
end krylov.Functions
