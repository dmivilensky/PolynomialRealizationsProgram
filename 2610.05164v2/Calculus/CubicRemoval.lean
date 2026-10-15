import «2610.05164v2».Calculus.CompactIntegral
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
Article: 2610.05164v2, Theorem 3.2.
Smooth removal of a cubic zero on a closed interval.
Use: `«2610.05164v2».Calculus.smooth_cubic_quotient` feeds
`«2610.05164v2».Calculus.regular_defect_cubic_quotient` (regular defect cubic quotient).
Proof chain: `«2610.05164v2».Calibration.ReferenceData.calibration_constant_normalized` —
2610.05164v2, Theorem 3.2; Constructed contact potential and calibrated reference.
Source: mathlib, Mathlib.Analysis.Calculus — parameter differentiation, Taylor integral remainder
and implicit-function calculus. The needed form is proved here.
-/
namespace «2610.05164v2».Calculus
noncomputable section
open Set Filter MeasureTheory Real
open scoped Topology ContDiff
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {β : ℝ} (hβ : 0<β) (D : ℕ → ℝ → ℝ)
  (hc : ∀ j, ContinuousOn (D j) (Icc 0 β))
  (hd : ∀ j, ∀ t ∈ Icc 0 β, HasDerivWithinAt (D j) (D (j+1) t) (Icc 0 β) t)

 /--
Defines `cubicIntegral` of type `ℝ` by `∫ v in Icc (0:ℝ) 1, (1-v)^2*v^j*D (j+3) (t*v)/2`.

Use: `«2610.05164v2».Calculus.cubicIntegral_factor` uses this definition to establish exact
identity `t^3*cubicIntegral D 0 t=D 0 t`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Source: mathlib, Mathlib.Analysis.Calculus — parameter differentiation, Taylor integral
remainder and implicit-function calculus.
-/
def cubicIntegral (D : ℕ → ℝ → ℝ) (j : ℕ) (t : ℝ) : ℝ :=
  ∫ v in Icc (0:ℝ) 1, (1-v)^2*v^j*D (j+3) (t*v)/2

 /--
Membership in the specified domain/enclosure: `t*v ∈ Icc 0 β`.

Use: `«2610.05164v2».Calculus.chain_continuous` uses this assertion to establish continuity on
the stated domain: `ContinuousOn (fun v => D j (t*v)) (Icc (0:ℝ) 1)`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Source: mathlib, Mathlib.Analysis.Calculus — parameter differentiation, Taylor integral
remainder and implicit-function calculus.

Proof: The displayed proof term instantiates the cited result with exactly the parameters and
hypotheses of this assertion.
-/
theorem mul_unit_mem {t v : ℝ} (ht : t ∈ Icc 0 β) (hv : v ∈ Icc (0:ℝ) 1) :
    t*v ∈ Icc 0 β :=
  ⟨mul_nonneg ht.1 hv.1,(mul_le_of_le_one_right ht.1 hv.2).trans ht.2⟩

include hc in
 /--
Continuity on the stated domain: `ContinuousOn (fun p : ℝ × ℝ => (1-p.2)^2*p.2^j*D (j+3)
(p.1*p.2)/2) (Icc 0 β ×ˢ Icc (0:ℝ) 1)`.

Use: `«2610.05164v2».Calculus.cubicIntegral_derivative` uses this continuity result to
establish the derivative within the stated domain: `HasDerivWithinAt (cubicIntegral D j)
(cubicIntegral D (j+1) t) (Icc 0 β) t`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Source: mathlib, Mathlib.Analysis.Calculus — parameter differentiation, Taylor integral
remainder and implicit-function calculus.

Proof: Use the identities/estimates `«2610.05164v2».Calculus.mul_unit_mem` with the arguments
shown in the proof.
-/
theorem cubic_integrand_continuous (j : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ => (1-p.2)^2*p.2^j*D (j+3) (p.1*p.2)/2)
      (Icc 0 β ×ˢ Icc (0:ℝ) 1) := by
  have hcomp := (hc (j+3)).comp (continuousOn_fst.mul continuousOn_snd)
    (fun (p : ℝ × ℝ) (hp : p ∈ Icc 0 β ×ˢ Icc (0:ℝ) 1) => mul_unit_mem hp.1 hp.2)
  exact (((continuousOn_const.sub continuousOn_snd).pow 2).mul
    (continuousOn_snd.pow j) |>.mul hcomp).div_const 2

include hd in
 /--
The actual derivative at the stated point: `HasDerivAt (fun t => (1-v)^2*v^j*D (j+3) (t*v)/2)
((1-v)^2*v^(j+1)*D (j+1+3) (t*v)/2) t`.

Use: `«2610.05164v2».Calculus.cubicIntegral_derivative` uses this derivative formula to
establish the derivative within the stated domain: `HasDerivWithinAt (cubicIntegral D j)
(cubicIntegral D (j+1) t) (Icc 0 β) t`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Source: mathlib, Mathlib.Analysis.Calculus — parameter differentiation, Taylor integral
remainder and implicit-function calculus.

Proof: Separate `v=0` from its negation; prove the goal under each of these mutually exclusive
hypotheses.
-/
theorem cubic_integrand_derivative (j : ℕ) {t v : ℝ} (ht : t ∈ Ioo 0 β)
    (hv : v ∈ Icc (0:ℝ) 1) :
    HasDerivAt (fun t => (1-v)^2*v^j*D (j+3) (t*v)/2)
      ((1-v)^2*v^(j+1)*D (j+1+3) (t*v)/2) t := by
  -- Separate `v=0` from its negation; prove the goal under each of these mutually exclusive
  -- hypotheses.
  by_cases hz : v=0
  · subst v
    simpa using hasDerivAt_const t ((0:ℝ)^j*D (j+3) 0/2)
  have hp : 0<v := lt_of_le_of_ne hv.1 (Ne.symm hz)
  have htv : t*v ∈ Ioo 0 β :=
    ⟨mul_pos ht.1 hp,(mul_le_of_le_one_right ht.1.le hv.2).trans_lt ht.2⟩
  have h := ((hd (j+3) (t*v) ⟨htv.1.le,htv.2.le⟩).hasDerivAt
    (Icc_mem_nhds htv.1 htv.2)).comp t ((hasDerivAt_id t).mul_const v)
  convert! (h.const_mul ((1-v)^2*v^j)).div_const 2 using 1
  simp only [show j+3+1=j+1+3 by omega,pow_succ]
  ring

include hβ hc hd in
 /--
Establishes the uniform, quantified assertion `∀ j, ContDiffOn ℝ ∞ (cubicIntegral D j) (Icc 0
β)`.

Use: `«2610.05164v2».Calculus.smooth_cubic_quotient` uses this assertion to establish
constructs witnesses with the exact properties `∃ g : ℝ → ℝ, ContDiffOn ℝ ∞ g (Icc 0 β) ∧ ∀ t ∈
Icc 0 β, f t=t^3*g t`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Source: mathlib, Mathlib.Analysis.Calculus — parameter differentiation, Taylor integral
remainder and implicit-function calculus.

Proof: Use the identities/estimates
`«2610.05164v2».Calculus.contDiffOn_compact_integral_of_derivatives`,
`«2610.05164v2».Calculus.cubic_integrand_continuous`,
`«2610.05164v2».Calculus.cubic_integrand_derivative` with the arguments shown in the proof.
-/
theorem cubicIntegral_smooth : ∀ j, ContDiffOn ℝ ∞ (cubicIntegral D j) (Icc 0 β) :=
  contDiffOn_compact_integral_of_derivatives hβ
    (fun j t v => (1-v)^2*v^j*D (j+3) (t*v)/2)
    (cubic_integrand_continuous D hc) (fun j _ ht _ hv => cubic_integrand_derivative D hd j ht hv)
include hβ hc hd in
 /--
The derivative within the stated domain: `HasDerivWithinAt (cubicIntegral D j) (cubicIntegral D
(j+1) t) (Icc 0 β) t`.

Use: `«2610.05164v2».Calculus.cubicIntegral_iterated_derivative` uses this derivative formula
to establish pointwise equality on the specified domain: `EqOn (iteratedDerivWithin j
(cubicIntegral D 0) (Icc 0 β)) (cubicIntegral D j) (Icc 0 β)`.

Article: 2610.05164v2, Theorem 3.2.

Source: mathlib, Mathlib.Analysis.Calculus — parameter differentiation, Taylor integral
remainder and implicit-function calculus.

Proof: Use the identities/estimates
`«2610.05164v2».Calculus.hasDerivWithinAt_compact_integral`,
`«2610.05164v2».Calculus.cubic_integrand_continuous`,
`«2610.05164v2».Calculus.cubic_integrand_derivative` with the arguments shown in the proof.
-/
theorem cubicIntegral_derivative (j : ℕ) {t : ℝ} (ht : t ∈ Icc 0 β) :
    HasDerivWithinAt (cubicIntegral D j) (cubicIntegral D (j+1) t) (Icc 0 β) t :=
  hasDerivWithinAt_compact_integral hβ (cubic_integrand_continuous D hc j)
    (cubic_integrand_continuous D hc (j+1))
    (fun _ ht _ hv => cubic_integrand_derivative D hd j ht hv) t ht

include hc in
 /--
Continuity on the stated domain: `ContinuousOn (fun v => D j (t*v)) (Icc (0:ℝ) 1)`.

Use: `«2610.05164v2».Calculus.weighted_parts` uses this continuity result to establish the
precise assertion is `-(r:ℝ)*(∫ v in Icc (0:ℝ) 1, (1-v)^(r-1)*D j (t*v))+ t*(∫ v in Icc (0:ℝ)
1, (1-v)^r*D (j+1) (t*v))= (0:ℝ)^r*D j t-D j 0`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Source: mathlib, Mathlib.Analysis.Calculus — parameter differentiation, Taylor integral
remainder and implicit-function calculus.

Proof: Use the identities/estimates `«2610.05164v2».Calculus.mul_unit_mem` with the arguments
shown in the proof.
-/
theorem chain_continuous (j : ℕ) {t : ℝ} (ht : t ∈ Icc 0 β) :
    ContinuousOn (fun v => D j (t*v)) (Icc (0:ℝ) 1) :=
  (hc j).comp (continuousOn_const.mul continuousOn_id) (fun _ hv => mul_unit_mem ht hv)

include hd in
 /--
The actual derivative at the stated point: `HasDerivAt (fun v => D j (t*v)) (t*D (j+1) (t*v))
v`.

Use: `«2610.05164v2».Calculus.weighted_parts` uses this derivative formula to establish the
precise assertion is `-(r:ℝ)*(∫ v in Icc (0:ℝ) 1, (1-v)^(r-1)*D j (t*v))+ t*(∫ v in Icc (0:ℝ)
1, (1-v)^r*D (j+1) (t*v))= (0:ℝ)^r*D j t-D j 0`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Source: mathlib, Mathlib.Analysis.Calculus — parameter differentiation, Taylor integral
remainder and implicit-function calculus.

Proof: Separate `t=0` from its negation; prove the goal under each of these mutually exclusive
hypotheses.
-/
theorem chain_derivative (j : ℕ) {t v : ℝ} (ht : t ∈ Icc 0 β)
    (hv : v ∈ Ioo (0:ℝ) 1) :
    HasDerivAt (fun v => D j (t*v)) (t*D (j+1) (t*v)) v := by
  -- Separate `t=0` from its negation; prove the goal under each of these mutually exclusive
  -- hypotheses.
  by_cases hz : t=0
  · subst t
    simpa only [zero_mul] using hasDerivAt_const v (D j 0)
  have hp : 0<t := lt_of_le_of_ne ht.1 (Ne.symm hz)
  have htv : t*v ∈ Ioo 0 β :=
    ⟨mul_pos hp hv.1,(mul_lt_of_lt_one_right hp hv.2).trans_le ht.2⟩
  convert! ((hd j (t*v) ⟨htv.1.le,htv.2.le⟩).hasDerivAt (Icc_mem_nhds htv.1 htv.2)).comp v
    ((hasDerivAt_id v).const_mul t) using 1
  ring

include hc hd in
 /--
The precise assertion is `-(r:ℝ)*(∫ v in Icc (0:ℝ) 1, (1-v)^(r-1)*D j (t*v))+ t*(∫ v in Icc
(0:ℝ) 1, (1-v)^r*D (j+1) (t*v))= (0:ℝ)^r*D j t-D j 0`.

Use: `«2610.05164v2».Calculus.cubicIntegral_factor` uses this identity to establish exact
identity `t^3*cubicIntegral D 0 t=D 0 t`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Source: mathlib, Mathlib.Analysis.Calculus — parameter differentiation, Taylor integral
remainder and implicit-function calculus.

Proof: Use the identities/estimates `«2610.05164v2».Calculus.chain_continuous`,
`«2610.05164v2».Calculus.chain_derivative` with the arguments shown in the proof.
-/
theorem weighted_parts (j r : ℕ) {t : ℝ} (ht : t ∈ Icc 0 β) :
    -(r:ℝ)*(∫ v in Icc (0:ℝ) 1, (1-v)^(r-1)*D j (t*v))+
      t*(∫ v in Icc (0:ℝ) 1, (1-v)^r*D (j+1) (t*v))=
      (0:ℝ)^r*D j t-D j 0 := by
  -- Use the identities/estimates `«2610.05164v2».Calculus.chain_continuous`,
  -- `«2610.05164v2».Calculus.chain_derivative` with the arguments shown in the proof.
  let f := fun v => (1-v)^r*D j (t*v)
  let g := fun v => -(r:ℝ)*((1-v)^(r-1)*D j (t*v))+t*((1-v)^r*D (j+1) (t*v))
  -- Establish continuity h₁ before using the function at limits or in calculus arguments.
  have h₁ : ContinuousOn (fun v => (1-v)^(r-1)*D j (t*v)) (Icc (0:ℝ) 1) :=
    ((continuousOn_const.sub continuousOn_id).pow _).mul (chain_continuous D hc j ht)
  -- Establish continuity h₂ before using the function at limits or in calculus arguments.
  have h₂ : ContinuousOn (fun v => (1-v)^r*D (j+1) (t*v)) (Icc (0:ℝ) 1) :=
    ((continuousOn_const.sub continuousOn_id).pow _).mul (chain_continuous D hc (j+1) ht)
  -- Establish continuity hcont before using the function at limits or in calculus arguments.
  have hcont : ContinuousOn f (Icc (0:ℝ) 1) :=
    ((continuousOn_const.sub continuousOn_id).pow _).mul (chain_continuous D hc j ht)
  have hderiv : ∀ v ∈ Ioo (0:ℝ) 1, HasDerivAt f (g v) v := by
    intro v hv
    convert! (((hasDerivAt_id v).const_sub 1).pow r).mul (chain_derivative D hd j ht hv) using 1
    dsimp only [g,Pi.pow_apply,id_eq]
    ring
  -- Establish continuity hg before using the function at limits or in calculus arguments.
  have hg : ContinuousOn g (Icc (0:ℝ) 1) :=
    (continuousOn_const.mul h₁).add (continuousOn_const.mul h₂)
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one hcont hderiv
    ((by simpa only [uIcc_of_le zero_le_one] using hg : ContinuousOn g (uIcc (0:ℝ) 1)).intervalIntegrable (μ := volume))
  rw [intervalIntegral.integral_of_le zero_le_one,← integral_Icc_eq_integral_Ioc] at he
  have hi := integral_add ((h₁.integrableOn_compact (μ := volume) isCompact_Icc).const_mul (-(r:ℝ)))
    ((h₂.integrableOn_compact (μ := volume) isCompact_Icc).const_mul t)
  dsimp only [g] at he
  rw [hi,integral_const_mul,integral_const_mul] at he
  simpa [f] using he

include hc hd in
 /--
Exact identity `t^3*cubicIntegral D 0 t=D 0 t`.

Use: `«2610.05164v2».Calculus.cubicIntegral_quotient` uses this identity to establish exact
identity `cubicIntegral D 0 t=D 0 t/t^3`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Source: mathlib, Mathlib.Analysis.Calculus — parameter differentiation, Taylor integral
remainder and implicit-function calculus.

Proof: Use the identities/estimates `«2610.05164v2».Calculus.weighted_parts` with the arguments
shown in the proof.
-/
theorem cubicIntegral_factor (h₀ : D 0 0=0) (h₁ : D 1 0=0) (h₂ : D 2 0=0)
    {t : ℝ} (ht : t ∈ Icc 0 β) : t^3*cubicIntegral D 0 t=D 0 t := by
  -- Use the identities/estimates `«2610.05164v2».Calculus.weighted_parts` with the arguments
  -- shown in the proof.
  have he₀ := weighted_parts D hc hd 0 0 ht
  have he₁ := weighted_parts D hc hd 1 1 ht
  have he₂ := weighted_parts D hc hd 2 2 ht
  norm_num [h₀,h₁,h₂] at he₀ he₁ he₂
  unfold cubicIntegral
  simp only [pow_zero,mul_one,integral_div]
  linear_combination he₀+t*he₁+t^2/2*he₂

include hc hd in
 /--
Exact identity `cubicIntegral D 0 t=D 0 t/t^3`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: 2610.05164v2, Theorem 3.2.

Source: mathlib, Mathlib.Analysis.Calculus — parameter differentiation, Taylor integral
remainder and implicit-function calculus.

Proof: Use the identities/estimates `«2610.05164v2».Calculus.cubicIntegral_factor` with the
arguments shown in the proof.
-/
theorem cubicIntegral_quotient (h₀ : D 0 0=0) (h₁ : D 1 0=0) (h₂ : D 2 0=0)
    {t : ℝ} (ht : t ∈ Ioo 0 β) : cubicIntegral D 0 t=D 0 t/t^3 := by
  have he := cubicIntegral_factor D hc hd h₀ h₁ h₂ ⟨ht.1.le,ht.2.le⟩
  exact (eq_div_iff (pow_ne_zero _ ht.1.ne')).mpr (by nlinarith [he])

include hβ in
 /--
Establishes the uniform, quantified assertion `∀ j, ∀ t ∈ Icc 0 β, HasDerivWithinAt
(iteratedDerivWithin j f (Icc 0 β)) (iteratedDerivWithin (j+1) f (Icc 0 β) t) (Icc 0 β) t`.

Use: `«2610.05164v2».Calculus.smooth_cubic_quotient` uses this assertion to establish
constructs witnesses with the exact properties `∃ g : ℝ → ℝ, ContDiffOn ℝ ∞ g (Icc 0 β) ∧ ∀ t ∈
Icc 0 β, f t=t^3*g t`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Source: mathlib, Mathlib.Analysis.Calculus — parameter differentiation, Taylor integral
remainder and implicit-function calculus.

Proof: Expand/rewrite the named definitions and identities appearing in the tactic block; the
remaining goal is a direct simplification or algebraic consequence.
-/
theorem closed_derivative_chain {f : ℝ → ℝ} (hf : ContDiffOn ℝ ∞ f (Icc 0 β)) :
    ∀ j, ∀ t ∈ Icc 0 β, HasDerivWithinAt (iteratedDerivWithin j f (Icc 0 β))
      (iteratedDerivWithin (j+1) f (Icc 0 β) t) (Icc 0 β) t := by
  intro j t ht
  rw [iteratedDerivWithin_succ]
  exact (hf.differentiableOn_iteratedDerivWithin (by exact_mod_cast (show (j:ℕ∞)<⊤ from ENat.natCast_lt_top j)) (uniqueDiffOn_Icc hβ) t ht).hasDerivWithinAt

include hβ in
/--
Every smooth function whose first three Taylor data vanish has a smooth cubic quotient on the
entire closed interval.

Constructs witnesses with the exact properties `∃ g : ℝ → ℝ, ContDiffOn ℝ ∞ g (Icc 0 β) ∧ ∀ t ∈
Icc 0 β, f t=t^3*g t`.

Use: `«2610.05164v2».Calculus.regular_defect_cubic_quotient` uses this identity to establish
constructs witnesses with the exact properties `∃ g : ℝ → ℝ, ContDiffOn ℝ ∞ g (Icc (0:ℝ) 1) ∧ ∀
t ∈ Icc (0:ℝ) 1, w t=t^3*g t`.

Article: 2610.05164v2, Theorem 3.6 via
`«2610.05164v2».DualCertificate.Data.admissible_analytic`.

Source: mathlib, Mathlib.Analysis.Calculus — parameter differentiation, Taylor integral
remainder and implicit-function calculus.

Proof: Use the identities/estimates `«2610.05164v2».Calculus.closed_derivative_chain`,
`«2610.05164v2».Calculus.cubicIntegral_smooth`, `«2610.05164v2».Calculus.cubicIntegral_factor`
with the arguments shown in the proof.
-/
theorem smooth_cubic_quotient {f : ℝ → ℝ} (hf : ContDiffOn ℝ ∞ f (Icc 0 β))
    (h₀ : f 0=0) (h₁ : derivWithin f (Icc 0 β) 0=0)
    (h₂ : iteratedDerivWithin 2 f (Icc 0 β) 0=0) :
    ∃ g : ℝ → ℝ, ContDiffOn ℝ ∞ g (Icc 0 β) ∧
      ∀ t ∈ Icc 0 β, f t=t^3*g t := by
  -- Use the identities/estimates `«2610.05164v2».Calculus.closed_derivative_chain`,
  -- `«2610.05164v2».Calculus.cubicIntegral_smooth`,
  -- `«2610.05164v2».Calculus.cubicIntegral_factor` with the arguments shown in the proof.
  let J := fun j => iteratedDerivWithin j f (Icc 0 β)
  have hJ : ∀ j, ContinuousOn (J j) (Icc 0 β) := fun j =>
    hf.continuousOn_iteratedDerivWithin (by exact_mod_cast (show (j:ℕ∞)≤⊤ from le_top)) (uniqueDiffOn_Icc hβ)
  have hdJ := closed_derivative_chain hβ hf
  refine ⟨cubicIntegral J 0,cubicIntegral_smooth hβ J hJ hdJ 0,?_⟩
  intro t ht
  exact (cubicIntegral_factor J hJ hdJ (by simpa [J] using h₀)
    (by simpa [J] using h₁) h₂ ht).symm

end
end «2610.05164v2».Calculus
