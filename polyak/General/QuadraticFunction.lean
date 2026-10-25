import polyak.Basic
import polyak.General.QuadraticDiagonal
import Mathlib.Analysis.InnerProductSpace.Calculus

/-! Article: the rate on quadratics in §6.1.
Genuine quadratic functions in arbitrary orthogonal coordinates, with
translated minimizers and arbitrary additive constants. Their gradients,
strong convexity and smoothness are proved from the symmetric Hessian and
its Rayleigh bounds, rather than assumed for a surrogate iteration. -/

noncomputable section
namespace polyak.General

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

def quadraticPotential (H : E→ₗ[ℝ]E) (a : E) (c : ℝ) (x : E) : ℝ :=
  (1/2:ℝ)*inner ℝ (H (x-a)) (x-a)+c

theorem hasGradientAt_quadraticPotential (H : E→ₗ[ℝ]E) (hH : H.IsSymmetric)
    (a : E) (c : ℝ) (x : E) :
    HasGradientAt (quadraticPotential H a c) (H (x-a)) x := by
  let Hc : E→L[ℝ]E := H.toContinuousLinearMap
  have hx := (hasFDerivAt_id (𝕜:=ℝ) x).sub_const a
  have hHderiv := Hc.hasFDerivAt.comp x hx
  rw [hasGradientAt_iff_hasFDerivAt]
  convert ((hHderiv.inner ℝ hx).const_mul (1/2:ℝ)).add_const c using 1
  · rfl
  · ext v
    change inner ℝ (H (x-a)) v=
      (1/2:ℝ)*(inner ℝ (H (x-a)) v+inner ℝ (H v) (x-a))
    rw [hH v (x-a),real_inner_comm v (H (x-a))]
    ring

theorem gradient_quadraticPotential (H : E→ₗ[ℝ]E) (hH : H.IsSymmetric)
    (a : E) (c : ℝ) (x : E) :
    gradient (quadraticPotential H a c) x=H (x-a) :=
  (hasGradientAt_quadraticPotential H hH a c x).gradient

omit [FiniteDimensional ℝ E] in
@[simp] theorem quadraticPotential_center (H : E→ₗ[ℝ]E) (a : E) (c : ℝ) :
    quadraticPotential H a c a=c := by simp [quadraticPotential]

theorem quadraticPotential_tangent_identity (H : E→ₗ[ℝ]E) (hH : H.IsSymmetric)
    (a : E) (c : ℝ) (x y : E) :
    quadraticPotential H a c y=quadraticPotential H a c x+
      inner ℝ (gradient (quadraticPotential H a c) x) (y-x)+
      (1/2:ℝ)*inner ℝ (H (y-x)) (y-x) := by
  rw [gradient_quadraticPotential H hH]
  have he : y-a=(x-a)+(y-x) := by abel
  unfold quadraticPotential
  rw [he,map_add,inner_add_left,inner_add_right,inner_add_right,
    hH (y-x) (x-a),real_inner_comm (y-x) (H (x-a))]
  ring

omit [FiniteDimensional ℝ E] in
theorem quadraticPotential_minimizer (H : E→ₗ[ℝ]E) {μ : ℝ} (hμ : 0≤μ)
    (hlower : ∀ v : E,μ*‖v‖^2≤ inner ℝ (H v) v) (a : E) (c : ℝ) (x : E) :
    quadraticPotential H a c a≤quadraticPotential H a c x := by
  rw [quadraticPotential_center]
  have hh:=hlower (x-a)
  have hn:=mul_nonneg hμ (sq_nonneg ‖x-a‖)
  unfold quadraticPotential
  linarith

/-- The matrix model really belongs to the original function class. -/
theorem quadraticPotential_smoothStronglyConvex (H : E→ₗ[ℝ]E)
    (hH : H.IsSymmetric) {μ L : ℝ} (hμ : 0<μ) (hμL : μ<L)
    (hlower : ∀ v : E,μ*‖v‖^2≤ inner ℝ (H v) v)
    (hupper : ∀ v : E,inner ℝ (H v) v≤L*‖v‖^2) (a : E) (c : ℝ) :
    SmoothStronglyConvex μ L (quadraticPotential H a c) := by
  refine ⟨hμ,hμL,fun x=>(hasGradientAt_quadraticPotential H hH a c x).differentiableAt,
    ?_,?_⟩
  · intro x y
    rw [quadraticPotential_tangent_identity H hH a c x y]
    have hh:=hlower (y-x)
    linarith
  · intro x y
    rw [gradient_quadraticPotential H hH,gradient_quadraticPotential H hH,← map_sub]
    have he : (x-a)-(y-a)=x-y := by abel
    rw [he]
    exact QuadraticDiagonal.norm_apply_le H hH hμ.le hlower hupper (hμ.trans hμL).le _

/-- The Rayleigh bounds characterize membership in the original function
class for a quadratic. They do not impose an extra regularity hypothesis. -/
theorem quadraticPotential_smoothStronglyConvex_iff (H : E→ₗ[ℝ]E)
    (hH : H.IsSymmetric) {μ L : ℝ} (hμ : 0<μ) (hμL : μ<L) (a : E) (c : ℝ) :
    SmoothStronglyConvex μ L (quadraticPotential H a c) ↔
      (∀ v : E,μ*‖v‖^2≤ inner ℝ (H v) v) ∧
      (∀ v : E,inner ℝ (H v) v≤L*‖v‖^2) := by
  constructor
  · intro hf
    constructor
    · intro v
      have hh:=hf.tangent_lower a (a+v)
      simp only [gradient_quadraticPotential H hH,sub_self,map_zero,
        inner_zero_left,add_zero,add_sub_cancel_left,quadraticPotential_center] at hh
      change c+μ/2*‖v‖^2≤(1/2:ℝ)*inner ℝ (H ((a+v)-a)) ((a+v)-a)+c at hh
      simp only [add_sub_cancel_left] at hh
      linarith
    · intro v
      have hh:=hf.grad_lipschitz (a+v) a
      simp only [gradient_quadraticPotential H hH,add_sub_cancel_left,
        sub_self,map_zero,sub_zero] at hh
      calc
        inner ℝ (H v) v≤‖H v‖*‖v‖ := real_inner_le_norm _ _
        _≤(L*‖v‖)*‖v‖ := mul_le_mul_of_nonneg_right hh (norm_nonneg _)
        _=L*‖v‖^2 := by ring
  · rintro ⟨hlower,hupper⟩
    exact quadraticPotential_smoothStronglyConvex H hH hμ hμL hlower hupper a c

/-- Positive definiteness supplies the center even for a quadratic written
with an arbitrary linear term. Thus the translated model loses no affine
quadratic objective. -/
theorem affine_quadratic_representation (H : E→ₗ[ℝ]E) (hH : H.IsSymmetric)
    {μ : ℝ} (hμ : 0<μ) (hlower : ∀ v : E,μ*‖v‖^2≤ inner ℝ (H v) v)
    (b : E) (c : ℝ) :
    ∃ a : E,∃ c' : ℝ,∀ x : E,
      (1/2:ℝ)*inner ℝ (H x) x+inner ℝ b x+c=quadraticPotential H a c' x := by
  have hinj : Function.Injective H := by
    apply (LinearMap.ker_eq_bot).mp
    apply LinearMap.ker_eq_bot'.mpr
    intro v hv
    have hh:=hlower v
    rw [hv,inner_zero_left] at hh
    have hn : ‖v‖^2=0 := by nlinarith [sq_nonneg ‖v‖]
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hn)
  obtain ⟨a,ha⟩:=LinearMap.surjective_of_injective hinj (-b)
  refine ⟨a,c-(1/2:ℝ)*inner ℝ (H a) a,?_⟩
  intro x
  have hcross : inner ℝ (H x) a= -inner ℝ b x := by
    rw [hH x a,ha,inner_neg_right,real_inner_comm x b]
  unfold quadraticPotential
  simp only [map_sub,inner_sub_left,inner_sub_right,ha,inner_neg_left,hcross]
  ring

end polyak.General
