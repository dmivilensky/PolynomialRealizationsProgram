import krylov.Functions.PlanarHessianBounds

/-!
Article: main_krylov, prop:Fcycle(iii), actual self-concordant planar sources.
Use: certify the original full scalar cubic from its genuine diagonal tensor
budget and the true derived scalar Hessian margin, keeping all actual
lower-order coefficients. Source: Banach's theorem and true Riesz calculus.
-/
namespace krylov.Functions
noncomputable section
open Set Metric krylov.Tensor.BinaryCubic krylov.Nonlinear
open scoped InnerProductSpace

/-- The full actual scalar cubic is self-concordant on every open convex
region whose original Hessian margin pays the actual tensor budget.
Article: main_krylov, prop:Fcycle(iii).
The scalar margin below is verified for the shrinking true-minimizer ball;
all function derivatives and tensor contractions are derived here. -/
theorem planeCubic_scaled_selfConcordant_margin (p r a q : ℝ)
    (hp : 0≤p) (ha : 0≤a) (hq : 0<q) (haq : a≤2*q^3)
    {t : krylov.Tensor.BinaryCubic} (ht : t.InBall)
    (U : Set Plane) (hUo : IsOpen U) (hUc : Convex ℝ U)
    (hmargin : ∀ x∈U, q^2≤1-a*p*‖planeTerminalOperator r t‖-a*‖x-planeOfPair (p,r*p)‖) :
    IsStandardSelfConcordantOn (planeCubicObjective p r (scaleBinaryCubic a t)) U := by
  let f := planeCubicObjective p r (scaleBinaryCubic a t)
  let H := planeCubicHessian p r (scaleBinaryCubic a t)
  let V := canonicalVariation (scaleBinaryCubic a t).tensor
  have hφ : Differentiable ℝ (fun x : Plane=>x 0) := (EuclideanSpace.proj (𝕜:=ℝ) (ι:=Fin 2) 0).differentiable
  have hψ : Differentiable ℝ (fun x : Plane=>x 1) := (EuclideanSpace.proj (𝕜:=ℝ) (ι:=Fin 2) 1).differentiable
  have hf : Differentiable ℝ f := by
    unfold f planeCubicObjective planarCubicObjective planarReferenceQuadratic planarValueFamily pairOfPlane
    fun_prop
  have hlo x (hx : x∈U) (v : Plane) : q^2*‖v‖^2≤ inner ℝ v (H x v) :=
    (mul_le_mul_of_nonneg_right (hmargin x hx) (sq_nonneg _)).trans (planeCubicHessian_scaled_lower p r a hp ha ht x v)
  have hsqrt x (hx : x∈U) (v : Plane) : q*‖v‖≤Real.sqrt (inner ℝ v (H x v)) := by
    have hn : 0≤ inner ℝ v (H x v) := (by positivity : 0≤q^2*‖v‖^2).trans (hlo x hx v)
    apply (sq_le_sq₀ (by positivity : 0≤q*‖v‖) (Real.sqrt_nonneg _)).mp
    rw [mul_pow,Real.sq_sqrt hn]
    exact hlo x hx v
  refine ⟨{
    open_domain := hUo
    convex_domain := hUc
    differentiable := hf.differentiableOn
    hessian := H
    variation := fun _=>V
    gradient_derivative := fun x _=>planeCubicGradient_hasFDerivAt p r (scaleBinaryCubic a t) x
    hessian_derivative := fun x _=>planeCubicHessian_hasFDerivAt p r (scaleBinaryCubic a t) x
    variation_continuous := continuous_const.continuousOn
    hessian_symmetric := fun x _=>planeCubicHessian_symmetric p r (scaleBinaryCubic a t) x
    hessian_nonnegative := fun x hx v=>(by positivity : 0≤q^2*‖v‖^2).trans (hlo x hx v)
    mixed := ?_ }⟩
  intro x hx u v w
  change |inner ℝ v (V u w)|≤_
  rw [show inner ℝ v (V u w)=a*t.tensor.form u v w from by
    dsimp only [V]
    rw [canonicalVariation_pair,scaleBinaryCubic_tensor_apply]]
  rw [abs_mul,abs_of_nonneg ha]
  have hb := mul_le_mul_of_nonneg_left (tensor_bound ht u v w) ha
  have hbudget := mul_le_mul_of_nonneg_right haq (by positivity : 0≤‖u‖*‖v‖*‖w‖)
  calc
    _ ≤ a*(‖u‖*‖v‖*‖w‖) := hb
    _ ≤ 2*(q*‖u‖)*(q*‖v‖)*(q*‖w‖) := by nlinarith only [hbudget]
    _ ≤ _ := by gcongr <;> exact hsqrt x hx _

end
end krylov.Functions
