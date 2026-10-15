import «2610.05164v2».Sobolev.CausalL2
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-!
Article: 2610.05164v2, Theorem 3.1.
The distributional/AE derivative is established for arbitrary L2 data, using the Lebesgue
differentiation theorem.
Use: `«2610.05164v2».Sobolev.causalValue_hasDerivAt_ae` feeds
`«2610.05164v2».Sobolev.causalValue_sobolev` (causal Value sobolev).
Proof chain: `«2610.05164v2».GroundState.GroundWitness.square_identity` — 2610.05164v2, Theorem 3.1;
Sharp ground-state variational principle, ODE, simplicity and intrinsic coordinate.
Source: Brezis, Functional Analysis, Sobolev Spaces and Partial Differential Equations —
one-dimensional H1 representation and reproducing kernel. The needed form is proved here.
-/
namespace «2610.05164v2».Sobolev
noncomputable section
open «2610.05164v2».Continuum Set MeasureTheory Real
open scoped InnerProductSpace
set_option backward.isDefEq.respectTransparency false

/--
Exact identity `rawFeature x t = sqrt 2*causalKernel x t`.

Use: `«2610.05164v2».Sobolev.causalKernel_product_integrable` rewrites with this identity to
establish integrability of the displayed function: `Integrable (fun t => causalKernel x t*g
t)`.

Article: 2610.05164v2, Theorem 3.1 via
`«2610.05164v2».GroundState.GroundWitness.square_identity`.

Source: Brezis, Functional Analysis, Sobolev Spaces and Partial Differential Equations —
one-dimensional H1 representation and reproducing kernel.

Proof: Separate `t ≤ x` from its negation; prove the goal under each of these mutually
exclusive hypotheses.
-/
theorem rawFeature_causal (x t : ℝ) : rawFeature x t = sqrt 2*causalKernel x t := by by_cases h : t ≤ x <;> simp [rawFeature, causalKernel, h]

/--
Integrability of the displayed function: `Integrable (fun t => causalKernel x t*g t)`.

Use: `«2610.05164v2».Sobolev.causalHead_integrable` uses this integrability result to establish
integrability on the stated domain: `IntegrableOn (fun t => exp t*g t) (Iic x)`.

Article: 2610.05164v2, Theorem 3.1 via
`«2610.05164v2».GroundState.GroundWitness.square_identity`.

Source: Brezis, Functional Analysis, Sobolev Spaces and Partial Differential Equations —
one-dimensional H1 representation and reproducing kernel.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection. Clear the denominators using the available nonzero
hypotheses, then verify the remaining algebraic identity.
-/
theorem causalKernel_product_integrable (g : FeatureSpace) (x : ℝ) :
    Integrable (fun t => causalKernel x t*g t) := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  have h := (L2.integrable_inner (𝕜 := ℝ) (feature x) g).const_mul (sqrt 2)⁻¹
  apply h.congr
  filter_upwards [feature_coe x] with t ht
  rw [ht]
  change (sqrt 2)⁻¹*(g t*rawFeature x t) = causalKernel x t*g t
  rw [rawFeature_causal]
  field_simp

/--
Integrability on the stated domain: `IntegrableOn (fun t => exp t*g t) (Iic x)`.

Use: `«2610.05164v2».Sobolev.causalValue_primitive` uses this integrability result to establish
exact identity `causalValue g x = exp (-x)*(exp a*causalValue g a+∫ t in a..x, exp t*g t)`.

Article: 2610.05164v2, Theorem 3.1 via
`«2610.05164v2».GroundState.GroundWitness.square_identity`.

Source: Brezis, Functional Analysis, Sobolev Spaces and Partial Differential Equations —
one-dimensional H1 representation and reproducing kernel.

Proof: Separate `t ≤ x` from its negation; prove the goal under each of these mutually
exclusive hypotheses. Clear the denominators using the available nonzero hypotheses, then
verify the remaining algebraic identity. Prove equality of functions by evaluating both sides
at an arbitrary argument.
-/
theorem causalHead_integrable (g : FeatureSpace) (x : ℝ) :
    IntegrableOn (fun t => exp t*g t) (Iic x) := by
  -- Separate `t ≤ x` from its negation; prove the goal under each of these mutually exclusive
  -- hypotheses.
  apply (integrable_indicator_iff measurableSet_Iic).mp
  have he : (Iic x).indicator (fun t => exp t*g t) =
      (fun t => exp x*(causalKernel x t*g t)) := by
    funext t
    by_cases h : t ≤ x
    · rw [indicator_of_mem (show t ∈ Iic x from h), causalKernel,
        indicator_of_mem (show t ∈ Iic x from h), exp_sub]
      field_simp
    · simp [causalKernel, h]
  rw [he]
  exact (causalKernel_product_integrable g x).const_mul (exp x)

/--
Exact identity `causalValue g x = exp (-x)*∫ t in Iic x, exp t*g t`.

Use: `«2610.05164v2».Sobolev.causalValue_head_mul` rewrites with this identity to establish
exact identity `exp x*causalValue g x = ∫ t in Iic x, exp t*g t`.

Article: 2610.05164v2, Theorem 3.1 via
`«2610.05164v2».GroundState.GroundWitness.square_identity`.

Source: Brezis, Functional Analysis, Sobolev Spaces and Partial Differential Equations —
one-dimensional H1 representation and reproducing kernel.

Proof: Separate `t ≤ x` from its negation; prove the goal under each of these mutually
exclusive hypotheses.
-/
theorem causalValue_head (g : FeatureSpace) (x : ℝ) :
    causalValue g x = exp (-x)*∫ t in Iic x, exp t*g t := by
  -- Separate `t ≤ x` from its negation; prove the goal under each of these mutually exclusive
  -- hypotheses.
  rw [causalValue_integral]
  have he (t : ℝ) : causalKernel x t*g t =
      exp (-x)*(Iic x).indicator (fun t => exp t*g t) t := by
    by_cases h : t ≤ x <;>
      simp [causalKernel, h, exp_sub, exp_neg, div_eq_mul_inv, mul_comm, mul_assoc]
  simp_rw [he]
  rw [integral_const_mul, integral_indicator measurableSet_Iic]

/--
Exact identity `exp x*causalValue g x = ∫ t in Iic x, exp t*g t`.

Use: `«2610.05164v2».Sobolev.causalValue_primitive` rewrites with this identity to establish
exact identity `causalValue g x = exp (-x)*(exp a*causalValue g a+∫ t in a..x, exp t*g t)`.

Article: 2610.05164v2, Theorem 3.1 via
`«2610.05164v2».GroundState.GroundWitness.square_identity`.

Source: Brezis, Functional Analysis, Sobolev Spaces and Partial Differential Equations —
one-dimensional H1 representation and reproducing kernel.

Proof: Use the identities/estimates `«2610.05164v2».Sobolev.causalValue_head` with the
arguments shown in the proof.
-/
theorem causalValue_head_mul (g : FeatureSpace) (x : ℝ) :
    exp x*causalValue g x = ∫ t in Iic x, exp t*g t := by rw [causalValue_head, ← mul_assoc, ← exp_add, add_neg_cancel, exp_zero, one_mul]

/--
The integrating-factor formula holds at every point, for any anchor.

Exact identity `causalValue g x = exp (-x)*(exp a*causalValue g a+∫ t in a..x, exp t*g t)`.

Use: `«2610.05164v2».Sobolev.causalValue_absolutelyContinuous` uses this identity to establish
absolute continuity on the specified interval: `AbsolutelyContinuousOnInterval (causalValue g)
a b`.

Article: 2610.05164v2, Theorem 3.1 via
`«2610.05164v2».GroundState.GroundWitness.square_identity`.

Source: Brezis, Functional Analysis, Sobolev Spaces and Partial Differential Equations —
one-dimensional H1 representation and reproducing kernel.

Proof: Use the proved fundamental theorem of calculus with its explicit integrability and
endpoint hypotheses.
-/
theorem causalValue_primitive (g : FeatureSpace) (a x : ℝ) :
    causalValue g x = exp (-x)*(exp a*causalValue g a+∫ t in a..x, exp t*g t) := by
  have h := intervalIntegral.integral_Iic_sub_Iic (causalHead_integrable g a) (causalHead_integrable g x)
  rw [← causalValue_head_mul g x, ← causalValue_head_mul g a] at h
  have he : exp a*causalValue g a+(∫ t in a..x, exp t*g t) = exp x*causalValue g x := by linarith
  rw [he, ← mul_assoc, ← exp_add, neg_add_cancel, exp_zero, one_mul]

/--
The stated quantitative bound `LocallyIntegrable (fun t => exp t*g t) volume`.

Use: `«2610.05164v2».Sobolev.causalValue_absolutelyContinuous` uses this identity to establish
absolute continuity on the specified interval: `AbsolutelyContinuousOnInterval (causalValue g)
a b`.

Article: 2610.05164v2, Theorem 3.1 via
`«2610.05164v2».GroundState.GroundWitness.square_identity`.

Source: Brezis, Functional Analysis, Sobolev Spaces and Partial Differential Equations —
one-dimensional H1 representation and reproducing kernel.

Proof: The displayed proof term instantiates the cited result with exactly the parameters and
hypotheses of this assertion.
-/
theorem causalHead_locallyIntegrable (g : FeatureSpace) :
    LocallyIntegrable (fun t => exp t*g t) volume :=
  ((Lp.memLp g).locallyIntegrable (by norm_num)).continuous_mul continuous_exp

/--
Absolute continuity on the specified interval: `AbsolutelyContinuousOnInterval (causalValue g)
a b`.

Use: `«2610.05164v2».Sobolev.causalValue_sobolev` uses this assertion to establish the stated
quantitative bound `SobolevRegular (causalValue g) (fun x => g x-causalValue g x)`.

Article: 2610.05164v2, Theorem 3.1 via
`«2610.05164v2».GroundState.GroundWitness.square_identity`.

Source: Brezis, Functional Analysis, Sobolev Spaces and Partial Differential Equations —
one-dimensional H1 representation and reproducing kernel.

Proof: Use the identities/estimates `«2610.05164v2».Sobolev.causalHead_locallyIntegrable`,
`«2610.05164v2».Sobolev.causalValue_primitive` with the arguments shown in the proof.
-/
theorem causalValue_absolutelyContinuous (g : FeatureSpace) (a b : ℝ) :
    AbsolutelyContinuousOnInterval (causalValue g) a b := by
  -- Use the identities/estimates `«2610.05164v2».Sobolev.causalHead_locallyIntegrable`,
  -- `«2610.05164v2».Sobolev.causalValue_primitive` with the arguments shown in the proof.
  have hg : IntervalIntegrable (fun t => exp t*g t) volume a b := by
    apply intervalIntegrable_iff.mpr
    exact ((causalHead_locallyIntegrable g).integrableOn_isCompact isCompact_uIcc).mono_set uIoc_subset_uIcc
  have hp := hg.absolutelyContinuousOnInterval_intervalIntegral (left_mem_uIcc : a ∈ uIcc a b)
  have hc : AbsolutelyContinuousOnInterval (fun _ : ℝ => exp a*causalValue g a) a b :=
    (contDiff_const.contDiffOn : ContDiffOn ℝ 1 (fun _ : ℝ => exp a*causalValue g a) (uIcc a b)).absolutelyContinuousOnInterval
  have he : AbsolutelyContinuousOnInterval (fun x : ℝ => exp (-x)) a b :=
    ((contDiff_exp.comp contDiff_neg).contDiffOn : ContDiffOn ℝ 1 (fun x : ℝ => exp (-x)) (uIcc a b)).absolutelyContinuousOnInterval
  apply (he.mul (hc.add hp)).congr
  intro x _
  exact (causalValue_primitive g a x).symm

/--
The distributional/AE derivative is established for arbitrary L2 data, using the Lebesgue
differentiation theorem.

Establishes the stated eventual or almost-everywhere assertion `∀ᵐ x, HasDerivAt (causalValue
g) (g x-causalValue g x) x`.

Use: `«2610.05164v2».Sobolev.causalValue_sobolev` uses this assertion to establish the stated
quantitative bound `SobolevRegular (causalValue g) (fun x => g x-causalValue g x)`.

Article: 2610.05164v2, Theorem 3.1 via
`«2610.05164v2».GroundState.GroundWitness.square_identity`.

Source: Brezis, Functional Analysis, Sobolev Spaces and Partial Differential Equations —
one-dimensional H1 representation and reproducing kernel.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection. Prove equality of functions by evaluating both
sides at an arbitrary argument.
-/
theorem causalValue_hasDerivAt_ae (g : FeatureSpace) :
    ∀ᵐ x, HasDerivAt (causalValue g) (g x-causalValue g x) x := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  filter_upwards [LocallyIntegrable.ae_hasDerivAt_integral (causalHead_locallyIntegrable g)] with x hx
  have hp := (hasDerivAt_const x (exp (0:ℝ)*causalValue g 0)).add (hx 0)
  have he := (hasDerivAt_exp (-x)).comp x (hasDerivAt_id x).neg
  have hd := he.mul hp
  change HasDerivAt (fun x => exp (-x)*(exp (0:ℝ)*causalValue g 0+
      ∫ t in (0:ℝ)..x, exp t*g t))
    (exp (-x)*(-1)*(exp (0:ℝ)*causalValue g 0+∫ t in (0:ℝ)..x, exp t*g t)+
      exp (-x)*(0+exp x*g x)) x at hd
  have hfun : (fun x => exp (-x)*(exp (0:ℝ)*causalValue g 0+
      ∫ t in (0:ℝ)..x, exp t*g t)) = causalValue g :=
    funext (fun x => (causalValue_primitive g 0 x).symm)
  rw [hfun] at hd
  convert hd using 1
  rw [causalValue_primitive g 0 x]
  have hexp : exp (-x)*exp x = 1 := by rw [← exp_add, neg_add_cancel, exp_zero]
  linear_combination -(g x)*hexp

end
end «2610.05164v2».Sobolev
