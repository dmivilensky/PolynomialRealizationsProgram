import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Asymptotics.Lemmas

/-!
Article: 2610.05164v2, Proposition 13.
Differentiating a product at a zero of its differentiable factor needs only continuity of the other
factor.
Use: `«2610.05164v2».Calculus.product_hasFDerivAt_at_zero` feeds
`«2610.05164v2».Calculus.finite_comparison_derivative` (finite comparison derivative).
Proof chain: `«2610.05164v2».Primal.familyConstraintMap_c1` — 2610.05164v2, Theorem 5.2; Contraction
implies exact feasible density, uniqueness, iteration error and energy bound.
Source: mathlib, Mathlib.Analysis.Calculus — parameter differentiation, Taylor integral remainder
and implicit-function calculus. The needed form is proved here.
-/
namespace «2610.05164v2».Calculus
noncomputable section
open Filter Asymptotics
open scoped Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

/--
The actual Fréchet derivative: `HasFDerivAt (fun y => g y*f y) ((g x) • L) x`.

Use: `«2610.05164v2».Calculus.finite_comparison_derivative` uses this Fréchet derivative
formula to establish the actual Fréchet derivative: `HasFDerivAt F (∫ t in (0:ℝ)..1,K b b t • v
t) b`.

Article: 2610.05164v2, Theorem 5.2 via `«2610.05164v2».Primal.familyConstraintMap_c1`.

Source: mathlib, Mathlib.Analysis.Calculus — parameter differentiation, Taylor integral
remainder and implicit-function calculus.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem product_hasFDerivAt_at_zero {f g : H → ℝ} {x : H} {L : H →L[ℝ] ℝ}
    (hf : HasFDerivAt f L x) (hzero : f x=0) (hg : ContinuousAt g x) :
    HasFDerivAt (fun y => g y*f y) ((g x) • L) x := by
  -- Prove equality of functions by evaluating both sides at an arbitrary argument.
  have hgo : (fun y => g y-g x)=o[𝓝 x] (fun _ => (1:ℝ)) :=
    (isLittleO_one_iff _).mpr (by simpa only [sub_self] using hg.tendsto.sub_const (g x))
  have hfo : f=O[𝓝 x] (fun y => y-x) := by simpa only [hzero,sub_zero] using hf.isBigO_sub
  have h1 : (fun y => (g y-g x)*f y)=o[𝓝 x] (fun y => y-x) := by
    simpa only [smul_eq_mul,one_smul] using hgo.smul_isBigO hfo
  have h2 := (hasFDerivAt_iff_isLittleO.mp hf).const_smul_left (g x)
  apply hasFDerivAt_iff_isLittleO.mpr
  convert! h1.add h2 using 1
  funext y
  simp only [hzero,mul_zero,sub_zero,smul_apply,Pi.smul_apply,smul_eq_mul]
  ring

end
end «2610.05164v2».Calculus
