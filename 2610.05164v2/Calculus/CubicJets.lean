import «2610.05164v2».Calculus.CubicRemoval
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
Article: 2610.05164v2, Lemma 22.
Lemma 22's normalized positive averaging weight.
Use: `«2610.05164v2».Calculus.cubic_jet_average_enclosure` feeds
`«2610.05164v2».Calculus.finite_cubicIntegral_jet_enclosure` (finite cubic Integral jet enclosure).
Proof chain: `«2610.05164v2».Calculus.removing_cubic_zero` — 2610.05164v2, Lemma 22; Removal of a
cubic zero at the available finite differentiability order.
Source: mathlib, Mathlib.Analysis.Calculus — parameter differentiation, Taylor integral remainder
and implicit-function calculus. The needed form is proved here.
-/
namespace «2610.05164v2».Calculus
noncomputable section
open Set MeasureTheory Real
open scoped ContDiff
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/--
Defines `cubicWeight` of type `ℝ` by `((j+1:ℕ):ℝ)*((j+2:ℕ):ℝ)*((j+3:ℕ):ℝ)/2*((1-v)^2*v^j)`.

Use: `«2610.05164v2».Calculus.cubicIntegral_normalized_jet` uses this definition to establish
the precise assertion is `iteratedDerivWithin j (cubicIntegral D 0) (Icc 0 β)
t/(j.factorial:ℝ)= ∫ v in Icc (0:ℝ) 1, cubicWeight j v*(D (j+3) (t*v)/((j+3).factorial:ℝ))`.

Article: 2610.05164v2, Lemma 22 via `«2610.05164v2».Calculus.removing_cubic_zero`.

Source: mathlib, Mathlib.Analysis.Calculus — parameter differentiation, Taylor integral
remainder and implicit-function calculus.
-/
def cubicWeight (j : ℕ) (v : ℝ) : ℝ :=
  ((j+1:ℕ):ℝ)*((j+2:ℕ):ℝ)*((j+3:ℕ):ℝ)/2*((1-v)^2*v^j)

/--
The stated quantitative bound `0≤cubicWeight j v`.

Use: `«2610.05164v2».Calculus.cubic_jet_average_enclosure` uses this bound to establish
membership in the specified domain/enclosure: `(∫ v in Icc (0:ℝ) 1, cubicWeight j v*f v) ∈ Icc
L U`.

Article: 2610.05164v2, Lemma 22 via `«2610.05164v2».Calculus.removing_cubic_zero`.

Source: mathlib, Mathlib.Analysis.Calculus — parameter differentiation, Taylor integral
remainder and implicit-function calculus.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem cubicWeight_nonneg (j : ℕ) {v : ℝ} (hv : v ∈ Icc (0:ℝ) 1) : 0≤cubicWeight j v := by
  unfold cubicWeight
  exact mul_nonneg (by positivity) (mul_nonneg (sq_nonneg _) (pow_nonneg hv.1 _))

/--
Exact identity `(∫ v in Icc (0:ℝ) 1, cubicWeight j v)=1`.

Use: `«2610.05164v2».Calculus.cubicIntegral_endpoint_jet` rewrites with this identity to
establish the precise assertion is `iteratedDerivWithin j (cubicIntegral D 0) (Icc 0 β)
0/(j.factorial:ℝ)= D (j+3) 0/((j+3).factorial:ℝ)`.

Article: 2610.05164v2, Lemma 22 via `«2610.05164v2».Calculus.removing_cubic_zero`.

Source: mathlib, Mathlib.Analysis.Calculus — parameter differentiation, Taylor integral
remainder and implicit-function calculus.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity. Prove equality of functions by evaluating both sides at an arbitrary
argument.
-/
theorem cubicWeight_integral (j : ℕ) : (∫ v in Icc (0:ℝ) 1, cubicWeight j v)=1 := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  rw [integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le zero_le_one]
  have he : (fun v : ℝ => (1-v)^2*v^j)=fun v => v^j-2*v^(j+1)+v^(j+2) := by
    funext v
    simp only [pow_succ]
    ring
  unfold cubicWeight
  rw [intervalIntegral.integral_const_mul,he]
  have hi (k : ℕ) : IntervalIntegrable (fun v : ℝ => v^k) volume 0 1 :=
    (continuous_id.pow k).intervalIntegrable 0 1
  rw [intervalIntegral.integral_add ((hi j).sub ((hi (j+1)).const_mul 2)) (hi (j+2)),
    intervalIntegral.integral_sub (hi j) ((hi (j+1)).const_mul 2),
    intervalIntegral.integral_const_mul,integral_pow,integral_pow,integral_pow]
  simp only [one_pow]
  norm_num
  field_simp
  ring

/--
Integrability on the stated domain: `IntegrableOn (cubicWeight j) (Icc (0:ℝ) 1)`.

Use: `«2610.05164v2».Calculus.cubic_jet_average_enclosure` uses this integrability result to
establish membership in the specified domain/enclosure: `(∫ v in Icc (0:ℝ) 1, cubicWeight j v*f
v) ∈ Icc L U`.

Article: 2610.05164v2, Lemma 22 via `«2610.05164v2».Calculus.removing_cubic_zero`.

Source: mathlib, Mathlib.Analysis.Calculus — parameter differentiation, Taylor integral
remainder and implicit-function calculus.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem cubicWeight_integrable (j : ℕ) : IntegrableOn (cubicWeight j) (Icc (0:ℝ) 1) :=
  (by unfold cubicWeight; fun_prop : Continuous (cubicWeight j)).continuousOn.integrableOn_compact (μ := volume) isCompact_Icc

/--
Membership in the specified domain/enclosure: `(∫ v in Icc (0:ℝ) 1, cubicWeight j v*f v) ∈ Icc
L U`.

Use: `«2610.05164v2».Calculus.cubicIntegral_normalized_jet_enclosure` uses this assertion to
establish membership in the specified domain/enclosure: `iteratedDerivWithin j (cubicIntegral D
0) (Icc 0 β) t/(j.factorial:ℝ)∈Icc L U`.

Article: 2610.05164v2, Lemma 22 via `«2610.05164v2».Calculus.removing_cubic_zero`.

Source: mathlib, Mathlib.Analysis.Calculus — parameter differentiation, Taylor integral
remainder and implicit-function calculus.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem cubic_jet_average_enclosure (j : ℕ) {f : ℝ → ℝ} (hf : ContinuousOn f (Icc (0:ℝ) 1))
    {L U : ℝ} (hb : ∀ v ∈ Icc (0:ℝ) 1, f v ∈ Icc L U) :
    (∫ v in Icc (0:ℝ) 1, cubicWeight j v*f v) ∈ Icc L U := by
  -- Establish continuity hi before using the function at limits or in calculus arguments.
  have hi := ((by unfold cubicWeight; fun_prop : Continuous (cubicWeight j)).continuousOn.mul hf).integrableOn_compact (μ := volume) isCompact_Icc
  have hL : (∫ v in Icc (0:ℝ) 1, cubicWeight j v*L)=L := by
    rw [integral_mul_const,cubicWeight_integral,one_mul]
  have hU : (∫ v in Icc (0:ℝ) 1, cubicWeight j v*U)=U := by
    rw [integral_mul_const,cubicWeight_integral,one_mul]
  constructor
  · rw [← hL]
    apply integral_mono_ae ((cubicWeight_integrable j).mul_const L) hi
    filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
    exact mul_le_mul_of_nonneg_left (hb v hv).1 (cubicWeight_nonneg j hv)
  · rw [← hU]
    apply integral_mono_ae hi ((cubicWeight_integrable j).mul_const U)
    filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
    exact mul_le_mul_of_nonneg_left (hb v hv).2 (cubicWeight_nonneg j hv)

 /--
Pointwise equality on the specified domain: `EqOn (iteratedDerivWithin j (cubicIntegral D 0)
(Icc 0 β)) (cubicIntegral D j) (Icc 0 β)`.

Use: `«2610.05164v2».Calculus.cubicIntegral_normalized_jet` rewrites with this pointwise
identity to establish `iteratedDerivWithin j (cubicIntegral D 0) (Icc
0 β) t/(j.factorial:ℝ)= ∫ v in Icc (0:ℝ) 1, cubicWeight j v*(D (j+3)
(t*v)/((j+3).factorial:ℝ))`.

Article: 2610.05164v2, Lemma 22.

Source: mathlib, Mathlib.Analysis.Calculus — parameter differentiation, Taylor integral
remainder and implicit-function calculus.

Proof: Induct on `j`; the recursive step uses the previous-stage assertion.
-/
theorem cubicIntegral_iterated_derivative {β : ℝ} (hβ : 0<β) (D : ℕ → ℝ → ℝ)
    (hc : ∀ j, ContinuousOn (D j) (Icc 0 β))
    (hd : ∀ j, ∀ t ∈ Icc 0 β, HasDerivWithinAt (D j) (D (j+1) t) (Icc 0 β) t)
    (j : ℕ) : EqOn (iteratedDerivWithin j (cubicIntegral D 0) (Icc 0 β))
      (cubicIntegral D j) (Icc 0 β) := by
  -- Induct on `j`; the recursive step uses the previous-stage assertion.
  induction j with
  | zero => intro t _; rfl
  | succ j ih =>
    intro t ht
    rw [iteratedDerivWithin_succ,derivWithin_congr ih (ih ht)]
    exact (cubicIntegral_derivative hβ D hc hd j ht).derivWithin (uniqueDiffOn_Icc hβ t ht)

/--
Formula (Lemma 22) in normalized Taylor jets, including t=0.

The precise assertion is `iteratedDerivWithin j (cubicIntegral D 0) (Icc 0 β)
t/(j.factorial:ℝ)= ∫ v in Icc (0:ℝ) 1, cubicWeight j v*(D (j+3) (t*v)/((j+3).factorial:ℝ))`.

Use: `«2610.05164v2».Calculus.cubicIntegral_endpoint_jet` rewrites with this identity to
establish the precise assertion is `iteratedDerivWithin j (cubicIntegral D 0) (Icc 0 β)
0/(j.factorial:ℝ)= D (j+3) 0/((j+3).factorial:ℝ)`.

Article: 2610.05164v2, Lemma 22.

Source: mathlib, Mathlib.Analysis.Calculus — parameter differentiation, Taylor integral
remainder and implicit-function calculus.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity. Prove equality of functions by evaluating both sides at an arbitrary
argument.
-/
theorem cubicIntegral_normalized_jet {β : ℝ} (hβ : 0<β) (D : ℕ → ℝ → ℝ)
    (hc : ∀ j, ContinuousOn (D j) (Icc 0 β))
    (hd : ∀ j, ∀ t∈Icc 0 β, HasDerivWithinAt (D j) (D (j+1) t) (Icc 0 β) t)
    (j : ℕ) {t : ℝ} (ht : t∈Icc 0 β) :
    iteratedDerivWithin j (cubicIntegral D 0) (Icc 0 β) t/(j.factorial:ℝ)=
      ∫ v in Icc (0:ℝ) 1, cubicWeight j v*(D (j+3) (t*v)/((j+3).factorial:ℝ)) := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  rw [cubicIntegral_iterated_derivative hβ D hc hd j ht,cubicIntegral,← integral_div]
  congr 1
  funext v
  unfold cubicWeight
  have hf : ((j+3).factorial:ℝ)=
      ((j+3:ℕ):ℝ)*((j+2:ℕ):ℝ)*((j+1:ℕ):ℝ)*(j.factorial:ℝ) := by
    simp only [show j+3=(j+2)+1 by omega,show j+2=(j+1)+1 by omega,
      Nat.factorial_succ,Nat.cast_mul]
    ring
  rw [hf]
  field_simp

 /--
The precise assertion is `iteratedDerivWithin j (cubicIntegral D 0) (Icc 0 β)
0/(j.factorial:ℝ)= D (j+3) 0/((j+3).factorial:ℝ)`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: 2610.05164v2, Lemma 22.

Source: mathlib, Mathlib.Analysis.Calculus — parameter differentiation, Taylor integral
remainder and implicit-function calculus.

Proof: Use the identities/estimates `«2610.05164v2».Calculus.cubicIntegral_normalized_jet`,
`«2610.05164v2».Calculus.cubicWeight_integral` with the arguments shown in the proof.
-/
theorem cubicIntegral_endpoint_jet {β : ℝ} (hβ : 0<β) (D : ℕ → ℝ → ℝ)
    (hc : ∀ j, ContinuousOn (D j) (Icc 0 β))
    (hd : ∀ j, ∀ t∈Icc 0 β, HasDerivWithinAt (D j) (D (j+1) t) (Icc 0 β) t)
    (j : ℕ) :
    iteratedDerivWithin j (cubicIntegral D 0) (Icc 0 β) 0/(j.factorial:ℝ)=
      D (j+3) 0/((j+3).factorial:ℝ) := by
  rw [cubicIntegral_normalized_jet hβ D hc hd j ⟨le_rfl,hβ.le⟩]
  simp only [zero_mul,integral_mul_const,cubicWeight_integral,one_mul]

 /--
Membership in the specified domain/enclosure: `iteratedDerivWithin j (cubicIntegral D 0) (Icc 0
β) t/(j.factorial:ℝ)∈Icc L U`.

Use: a standalone supporting assertion for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: 2610.05164v2, Lemma 22.

Source: mathlib, Mathlib.Analysis.Calculus — parameter differentiation, Taylor integral
remainder and implicit-function calculus.

Proof: Use the identities/estimates `«2610.05164v2».Calculus.cubicIntegral_normalized_jet`,
`«2610.05164v2».Calculus.cubic_jet_average_enclosure`,
`«2610.05164v2».Calculus.chain_continuous` with the arguments shown in the proof.
-/
theorem cubicIntegral_normalized_jet_enclosure {β : ℝ} (hβ : 0<β) (D : ℕ → ℝ → ℝ)
    (hc : ∀ j, ContinuousOn (D j) (Icc 0 β))
    (hd : ∀ j, ∀ t∈Icc 0 β, HasDerivWithinAt (D j) (D (j+1) t) (Icc 0 β) t)
    (j : ℕ) {t L U : ℝ} (ht : t∈Icc 0 β)
    (hb : ∀ z∈Icc 0 t, D (j+3) z/((j+3).factorial:ℝ)∈Icc L U) :
    iteratedDerivWithin j (cubicIntegral D 0) (Icc 0 β) t/(j.factorial:ℝ)∈Icc L U := by
  -- Use the identities/estimates `«2610.05164v2».Calculus.cubicIntegral_normalized_jet`,
  -- `«2610.05164v2».Calculus.cubic_jet_average_enclosure`,
  -- `«2610.05164v2».Calculus.chain_continuous` with the arguments shown in the proof.
  rw [cubicIntegral_normalized_jet hβ D hc hd j ht]
  apply cubic_jet_average_enclosure j ((chain_continuous D hc (j+3) ht).div_const _)
  intro v hv
  exact hb (t*v) ⟨mul_nonneg ht.1 hv.1,mul_le_of_le_one_right ht.1 hv.2⟩

end
end «2610.05164v2».Calculus
