import «2610.05164v2».Calculus.CubicJets
import «2610.05164v2».Calculus.FiniteCompactIntegral

/-!
Article: 2610.05164v2, Lemma 22.
Lemma 22 with its literal finite differentiability assumption.
Use: `«2610.05164v2».Calculus.finite_cubicIntegral_factor` feeds
`«2610.05164v2».Calculus.removing_cubic_zero` (removing cubic zero).
Proof chain: `«2610.05164v2».Calculus.removing_cubic_zero` — 2610.05164v2, Lemma 22; Removal of a
cubic zero at the available finite differentiability order.
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

 /--
Continuity on the stated domain: `ContinuousOn (fun p : ℝ × ℝ => (1-p.2)^2*p.2^j*D (j+3)
(p.1*p.2)/2) (Icc 0 β ×ˢ Icc (0:ℝ) 1)`.

Use: `«2610.05164v2».Calculus.finite_cubicIntegral_derivative` uses this continuity result to
establish the derivative within the stated domain: `HasDerivWithinAt (cubicIntegral D j)
(cubicIntegral D (j+1) t) (Icc 0 β) t`.

Article: 2610.05164v2, Lemma 22 via `«2610.05164v2».Calculus.removing_cubic_zero`.

Source: mathlib, Mathlib.Analysis.Calculus — parameter differentiation, Taylor integral
remainder and implicit-function calculus.

Proof: Use the identities/estimates `«2610.05164v2».Calculus.mul_unit_mem` with the arguments
shown in the proof.
-/
theorem finite_cubic_integrand_continuous {β : ℝ} (D : ℕ → ℝ → ℝ) (j : ℕ)
    (hc : ContinuousOn (D (j+3)) (Icc 0 β)) :
    ContinuousOn (fun p : ℝ × ℝ => (1-p.2)^2*p.2^j*D (j+3) (p.1*p.2)/2)
      (Icc 0 β ×ˢ Icc (0:ℝ) 1) := by
  have hcomp := hc.comp (continuousOn_fst.mul continuousOn_snd)
    (fun (p : ℝ × ℝ) (hp : p∈Icc 0 β ×ˢ Icc (0:ℝ) 1) => mul_unit_mem hp.1 hp.2)
  exact (((continuousOn_const.sub continuousOn_snd).pow 2).mul
    (continuousOn_snd.pow j) |>.mul hcomp).div_const 2

 /--
The actual derivative at the stated point: `HasDerivAt (fun t => (1-v)^2*v^j*D (j+3) (t*v)/2)
((1-v)^2*v^(j+1)*D (j+1+3) (t*v)/2) t`.

Use: `«2610.05164v2».Calculus.finite_cubicIntegral_derivative` uses this derivative formula to
establish the derivative within the stated domain: `HasDerivWithinAt (cubicIntegral D j)
(cubicIntegral D (j+1) t) (Icc 0 β) t`.

Article: 2610.05164v2, Lemma 22 via `«2610.05164v2».Calculus.removing_cubic_zero`.

Source: mathlib, Mathlib.Analysis.Calculus — parameter differentiation, Taylor integral
remainder and implicit-function calculus.

Proof: Separate `v=0` from its negation; prove the goal under each of these mutually exclusive
hypotheses.
-/
theorem finite_cubic_integrand_derivative {β : ℝ} (D : ℕ → ℝ → ℝ) (j : ℕ)
    (hd : ∀ z∈Icc 0 β, HasDerivWithinAt (D (j+3)) (D (j+4) z) (Icc 0 β) z)
    {t v : ℝ} (ht : t∈Ioo 0 β) (hv : v∈Icc (0:ℝ) 1) :
    HasDerivAt (fun t => (1-v)^2*v^j*D (j+3) (t*v)/2)
      ((1-v)^2*v^(j+1)*D (j+1+3) (t*v)/2) t := by
  -- Separate `v=0` from its negation; prove the goal under each of these mutually exclusive
  -- hypotheses.
  by_cases hz : v=0
  · subst v
    simpa using hasDerivAt_const t ((0:ℝ)^j*D (j+3) 0/2)
  have hp : 0<v := lt_of_le_of_ne hv.1 (Ne.symm hz)
  have htv : t*v∈Ioo 0 β :=
    ⟨mul_pos ht.1 hp,(mul_le_of_le_one_right ht.1.le hv.2).trans_lt ht.2⟩
  have h := ((hd (t*v) ⟨htv.1.le,htv.2.le⟩).hasDerivAt
    (Icc_mem_nhds htv.1 htv.2)).comp t ((hasDerivAt_id t).mul_const v)
  convert! (h.const_mul ((1-v)^2*v^j)).div_const 2 using 1
  simp only [show j+4=j+1+3 by omega,pow_succ]
  ring

 /--
Smoothness to the stated order: `ContDiffOn ℝ n (cubicIntegral D 0) (Icc 0 β)`.

Use: `«2610.05164v2».Calculus.finite_cubic_quotient` uses this assertion to establish
constructs witnesses with the exact properties `∃ g : ℝ → ℝ,ContDiffOn ℝ (N+1) g (Icc 0 β) ∧ (∀
t∈Icc 0 β,f t=t^3*g t)`.

Article: 2610.05164v2, Lemma 22 via `«2610.05164v2».Calculus.removing_cubic_zero`.

Source: mathlib, Mathlib.Analysis.Calculus — parameter differentiation, Taylor integral
remainder and implicit-function calculus.

Proof: Use the identities/estimates `«2610.05164v2».Calculus.finite_compact_integral_smooth`,
`«2610.05164v2».Calculus.finite_cubic_integrand_continuous`,
`«2610.05164v2».Calculus.finite_cubic_integrand_derivative` with the arguments shown in the
proof.
-/
theorem finite_cubicIntegral_smooth {β : ℝ} (hβ : 0<β) (n : ℕ) (D : ℕ → ℝ → ℝ)
    (hc : ∀ j≤n+3, ContinuousOn (D j) (Icc 0 β))
    (hd : ∀ j<n+3, ∀ t∈Icc 0 β, HasDerivWithinAt (D j) (D (j+1) t) (Icc 0 β) t) :
    ContDiffOn ℝ n (cubicIntegral D 0) (Icc 0 β) := by
  -- Use the identities/estimates `«2610.05164v2».Calculus.finite_compact_integral_smooth`,
  -- `«2610.05164v2».Calculus.finite_cubic_integrand_continuous`,
  -- `«2610.05164v2».Calculus.finite_cubic_integrand_derivative` with the arguments shown in
  -- the proof.
  exact finite_compact_integral_smooth hβ n
    (fun j t v => (1-v)^2*v^j*D (j+3) (t*v)/2)
    (fun j hj => finite_cubic_integrand_continuous D j (hc (j+3) (by omega)))
    (fun j hj _ ht _ hv => finite_cubic_integrand_derivative D j
      (by simpa only [show j+3+1=j+4 by omega] using hd (j+3) (by omega)) ht hv) n 0 (by omega)

 /--
The derivative within the stated domain: `HasDerivWithinAt (cubicIntegral D j) (cubicIntegral D
(j+1) t) (Icc 0 β) t`.

Use: `«2610.05164v2».Calculus.cubic_taylor_enclosure` uses this derivative formula to establish
the identity stated in that declaration.

Article: 2610.05164v2, Lemma 22 via `«2610.05164v2».Calculus.removing_cubic_zero`.

Source: mathlib, Mathlib.Analysis.Calculus — parameter differentiation, Taylor integral
remainder and implicit-function calculus.

Proof: Use the identities/estimates
`«2610.05164v2».Calculus.hasDerivWithinAt_compact_integral`,
`«2610.05164v2».Calculus.finite_cubic_integrand_continuous`,
`«2610.05164v2».Calculus.finite_cubic_integrand_derivative` with the arguments shown in the
proof.
-/
theorem finite_cubicIntegral_derivative {β : ℝ} (hβ : 0<β) (D : ℕ → ℝ → ℝ) (j : ℕ)
    (hc : ContinuousOn (D (j+3)) (Icc 0 β)) (hc' : ContinuousOn (D (j+4)) (Icc 0 β))
    (hd : ∀ t∈Icc 0 β, HasDerivWithinAt (D (j+3)) (D (j+4) t) (Icc 0 β) t)
    {t : ℝ} (ht : t∈Icc 0 β) :
    HasDerivWithinAt (cubicIntegral D j) (cubicIntegral D (j+1) t) (Icc 0 β) t := by
  apply hasDerivWithinAt_compact_integral hβ (finite_cubic_integrand_continuous D j hc)
    (finite_cubic_integrand_continuous D (j+1) (by simpa only [show j+1+3=j+4 by omega] using hc'))
    (fun _ ht _ hv => finite_cubic_integrand_derivative D j hd ht hv) t ht

 /--
Exact identity `-(r:ℝ)*(∫ v in Icc (0:ℝ) 1,(1-v)^(r-1)*f (t*v))+ t*(∫ v in Icc (0:ℝ)
1,(1-v)^r*g (t*v))=(0:ℝ)^r*f t-f 0`.

Use: `«2610.05164v2».Calculus.finite_cubicIntegral_factor` uses this identity to establish
exact identity `t^3*cubicIntegral D 0 t=D 0 t`.

Article: 2610.05164v2, Lemma 22 via `«2610.05164v2».Calculus.removing_cubic_zero`.

Source: mathlib, Mathlib.Analysis.Calculus — parameter differentiation, Taylor integral
remainder and implicit-function calculus.

Proof: Separate `t=0` from its negation; prove the goal under each of these mutually exclusive
hypotheses.
-/
theorem weighted_parts_pair {β : ℝ} {f g : ℝ → ℝ}
    (hf : ContinuousOn f (Icc 0 β)) (hg : ContinuousOn g (Icc 0 β))
    (hd : ∀ z∈Icc 0 β,HasDerivWithinAt f (g z) (Icc 0 β) z)
    (r : ℕ) {t : ℝ} (ht : t∈Icc 0 β) :
    -(r:ℝ)*(∫ v in Icc (0:ℝ) 1,(1-v)^(r-1)*f (t*v))+
      t*(∫ v in Icc (0:ℝ) 1,(1-v)^r*g (t*v))=(0:ℝ)^r*f t-f 0 := by
  -- Establish continuity hcf before using the function at limits or in calculus arguments.
  have hcf : ContinuousOn (fun v => f (t*v)) (Icc (0:ℝ) 1) :=
    hf.comp (continuousOn_const.mul continuousOn_id) (fun _ hv => mul_unit_mem ht hv)
  -- Establish continuity hcg before using the function at limits or in calculus arguments.
  have hcg : ContinuousOn (fun v => g (t*v)) (Icc (0:ℝ) 1) :=
    hg.comp (continuousOn_const.mul continuousOn_id) (fun _ hv => mul_unit_mem ht hv)
  have hderiv : ∀ v∈Ioo (0:ℝ) 1,HasDerivAt (fun v => f (t*v)) (t*g (t*v)) v := by
    intro v hv
    by_cases hz : t=0
    · subst t
      simpa only [zero_mul] using hasDerivAt_const v (f 0)
    have hp : 0<t := lt_of_le_of_ne ht.1 (Ne.symm hz)
    have htv : t*v∈Ioo 0 β :=
      ⟨mul_pos hp hv.1,(mul_lt_of_lt_one_right hp hv.2).trans_le ht.2⟩
    convert! ((hd (t*v) ⟨htv.1.le,htv.2.le⟩).hasDerivAt (Icc_mem_nhds htv.1 htv.2)).comp v
      ((hasDerivAt_id v).const_mul t) using 1
    ring
  let F := fun v => (1-v)^r*f (t*v)
  let G := fun v => -(r:ℝ)*((1-v)^(r-1)*f (t*v))+t*((1-v)^r*g (t*v))
  -- Establish continuity h₁ before using the function at limits or in calculus arguments.
  have h₁ : ContinuousOn (fun v => (1-v)^(r-1)*f (t*v)) (Icc (0:ℝ) 1) :=
    ((continuousOn_const.sub continuousOn_id).pow (r-1)).mul hcf
  -- Establish continuity h₂ before using the function at limits or in calculus arguments.
  have h₂ : ContinuousOn (fun v => (1-v)^r*g (t*v)) (Icc (0:ℝ) 1) :=
    ((continuousOn_const.sub continuousOn_id).pow r).mul hcg
  -- Establish continuity hF before using the function at limits or in calculus arguments.
  have hF : ContinuousOn F (Icc (0:ℝ) 1) := ((continuousOn_const.sub continuousOn_id).pow r).mul hcf
  -- Establish continuity hG before using the function at limits or in calculus arguments.
  have hG : ContinuousOn G (Icc (0:ℝ) 1) := (continuousOn_const.mul h₁).add (continuousOn_const.mul h₂)
  have hdF : ∀ v∈Ioo (0:ℝ) 1,HasDerivAt F (G v) v := by
    intro v hv
    convert! (((hasDerivAt_id v).const_sub 1).pow r).mul (hderiv v hv) using 1
    dsimp only [G,Pi.pow_apply,id_eq]
    ring
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one hF hdF
    ((by simpa only [uIcc_of_le zero_le_one] using hG : ContinuousOn G (uIcc (0:ℝ) 1)).intervalIntegrable (μ := volume))
  rw [intervalIntegral.integral_of_le zero_le_one,← integral_Icc_eq_integral_Ioc] at he
  dsimp only [G] at he
  rw [integral_add ((h₁.integrableOn_compact (μ := volume) isCompact_Icc).const_mul (-(r:ℝ)))
    ((h₂.integrableOn_compact (μ := volume) isCompact_Icc).const_mul t),integral_const_mul,integral_const_mul] at he
  simpa [F] using he

 /--
Exact identity `t^3*cubicIntegral D 0 t=D 0 t`.

Use: `«2610.05164v2».Calculus.finite_cubic_quotient` uses this identity to establish constructs
witnesses with the exact properties `∃ g : ℝ → ℝ,ContDiffOn ℝ (N+1) g (Icc 0 β) ∧ (∀ t∈Icc 0
β,f t=t^3*g t)`.

Article: 2610.05164v2, Lemma 22 via `«2610.05164v2».Calculus.removing_cubic_zero`.

Source: mathlib, Mathlib.Analysis.Calculus — parameter differentiation, Taylor integral
remainder and implicit-function calculus.

Proof: Use the identities/estimates `«2610.05164v2».Calculus.weighted_parts_pair` with the
arguments shown in the proof.
-/
theorem finite_cubicIntegral_factor {β : ℝ} (D : ℕ → ℝ → ℝ)
    (hc : ∀ j≤3,ContinuousOn (D j) (Icc 0 β))
    (hd : ∀ j<3,∀ t∈Icc 0 β,HasDerivWithinAt (D j) (D (j+1) t) (Icc 0 β) t)
    (h₀ : D 0 0=0) (h₁ : D 1 0=0) (h₂ : D 2 0=0)
    {t : ℝ} (ht : t∈Icc 0 β) : t^3*cubicIntegral D 0 t=D 0 t := by
  -- Use the identities/estimates `«2610.05164v2».Calculus.weighted_parts_pair` with the
  -- arguments shown in the proof.
  have he₀ := weighted_parts_pair (hc 0 (by omega)) (hc 1 (by omega)) (hd 0 (by omega)) 0 ht
  have he₁ := weighted_parts_pair (hc 1 (by omega)) (hc 2 (by omega)) (hd 1 (by omega)) 1 ht
  have he₂ := weighted_parts_pair (hc 2 (by omega)) (hc 3 (by omega)) (hd 2 (by omega)) 2 ht
  norm_num [h₀,h₁,h₂] at he₀ he₁ he₂
  unfold cubicIntegral
  simp only [pow_zero,mul_one,integral_div]
  linear_combination he₀+t*he₁+t^2/2*he₂

 /--
Constructs witnesses with the exact properties `∃ g : ℝ → ℝ,ContDiffOn ℝ (N+1) g (Icc 0 β) ∧ (∀
t∈Icc 0 β,f t=t^3*g t)`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: 2610.05164v2, Lemma 22.

Source: mathlib, Mathlib.Analysis.Calculus — parameter differentiation, Taylor integral
remainder and implicit-function calculus.

Proof: Use the identities/estimates `«2610.05164v2».Calculus.finite_cubicIntegral_smooth`,
`«2610.05164v2».Calculus.finite_cubicIntegral_factor` with the arguments shown in the proof.
-/
theorem finite_cubic_quotient {β : ℝ} (hβ : 0<β) (N : ℕ) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ (N+4) f (Icc 0 β))
    (h₀ : f 0=0) (h₁ : derivWithin f (Icc 0 β) 0=0)
    (h₂ : iteratedDerivWithin 2 f (Icc 0 β) 0=0) :
    ∃ g : ℝ → ℝ,ContDiffOn ℝ (N+1) g (Icc 0 β) ∧
      (∀ t∈Icc 0 β,f t=t^3*g t) := by
  -- Use the identities/estimates `«2610.05164v2».Calculus.finite_cubicIntegral_smooth`,
  -- `«2610.05164v2».Calculus.finite_cubicIntegral_factor` with the arguments shown in the
  -- proof.
  let D := fun j => iteratedDerivWithin j f (Icc 0 β)
  have hc : ∀ j≤N+4,ContinuousOn (D j) (Icc 0 β) := fun j hj =>
    hf.continuousOn_iteratedDerivWithin (by exact_mod_cast hj) (uniqueDiffOn_Icc hβ)
  have hd : ∀ j<N+4,∀ t∈Icc 0 β,HasDerivWithinAt (D j) (D (j+1) t) (Icc 0 β) t := by
    intro j hj t ht
    dsimp only [D]
    rw [iteratedDerivWithin_succ]
    exact (hf.differentiableOn_iteratedDerivWithin (by exact_mod_cast hj) (uniqueDiffOn_Icc hβ) t ht).hasDerivWithinAt
  refine ⟨cubicIntegral D 0,finite_cubicIntegral_smooth hβ (N+1) D
    (fun j hj => hc j (by omega)) (fun j hj => hd j (by omega)),?_⟩
  intro t ht
  exact (finite_cubicIntegral_factor D (fun j hj => hc j (by omega))
    (fun j hj => hd j (by omega)) (by simpa [D] using h₀) (by simpa [D] using h₁) h₂ ht).symm

end
end «2610.05164v2».Calculus
