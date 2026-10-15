import «2610.05164v2».Calculus.FiniteCubicRemoval

/-!
Article: 2610.05164v2, Lemma 22.
Finite-order normalized quotient jets and their certified convex-hull bounds.
Use: `«2610.05164v2».Calculus.finite_cubicIntegral_jet_enclosure` feeds
`«2610.05164v2».Calculus.cubic_taylor_enclosure` (cubic taylor enclosure).
Proof chain: `«2610.05164v2».Calculus.removing_cubic_zero` — 2610.05164v2, Lemma 22; Removal of a
cubic zero at the available finite differentiability order.
Source: mathlib, Mathlib.Analysis.Calculus — parameter differentiation, Taylor integral remainder
and implicit-function calculus. The needed form is proved here.
-/
namespace «2610.05164v2».Calculus
noncomputable section
open Set MeasureTheory Real
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

 /--
Establishes the uniform, quantified assertion `∀ j≤n,EqOn (iteratedDerivWithin j (cubicIntegral
D 0) (Icc 0 β)) (cubicIntegral D j) (Icc 0 β)`.

Use: `«2610.05164v2».Calculus.finite_cubicIntegral_normalized_jet` rewrites with this bound to
establish the precise assertion is `iteratedDerivWithin j (cubicIntegral D 0) (Icc 0 β)
t/(j.factorial:ℝ)= ∫ v in Icc (0:ℝ) 1,cubicWeight j v*(D (j+3) (t*v)/((j+3).factorial:ℝ))`.

Article: 2610.05164v2, Lemma 22 via `«2610.05164v2».Calculus.removing_cubic_zero`.

Source: mathlib, Mathlib.Analysis.Calculus — parameter differentiation, Taylor integral
remainder and implicit-function calculus.

Proof: Induct on `j`; the recursive step uses the previous-stage assertion.
-/
theorem finite_cubicIntegral_iterated {β : ℝ} (hβ : 0<β) (n : ℕ) (D : ℕ → ℝ → ℝ)
    (hc : ∀ j≤n+3,ContinuousOn (D j) (Icc 0 β))
    (hd : ∀ j<n+3,∀ t∈Icc 0 β,HasDerivWithinAt (D j) (D (j+1) t) (Icc 0 β) t) :
    ∀ j≤n,EqOn (iteratedDerivWithin j (cubicIntegral D 0) (Icc 0 β)) (cubicIntegral D j) (Icc 0 β) := by
  -- Induct on `j`; the recursive step uses the previous-stage assertion.
  intro j
  induction j with
  | zero => intro _ t _;rfl
  | succ j ih =>
    intro hj t ht
    rw [iteratedDerivWithin_succ,derivWithin_congr (ih (by omega)) (ih (by omega) ht)]
    exact (finite_cubicIntegral_derivative hβ D j (hc (j+3) (by omega))
      (hc (j+4) (by omega)) (by simpa only [show j+3+1=j+4 by omega] using hd (j+3) (by omega)) ht).derivWithin
        (uniqueDiffOn_Icc hβ t ht)

 /--
The precise assertion is `iteratedDerivWithin j (cubicIntegral D 0) (Icc 0 β)
t/(j.factorial:ℝ)= ∫ v in Icc (0:ℝ) 1,cubicWeight j v*(D (j+3) (t*v)/((j+3).factorial:ℝ))`.

Use: `«2610.05164v2».Calculus.finite_cubicIntegral_endpoint_jet` rewrites with this identity to
establish the precise assertion is `iteratedDerivWithin j (cubicIntegral D 0) (Icc 0 β)
0/(j.factorial:ℝ)= D (j+3) 0/((j+3).factorial:ℝ)`.

Article: 2610.05164v2, Lemma 22 via `«2610.05164v2».Calculus.removing_cubic_zero`.

Source: mathlib, Mathlib.Analysis.Calculus — parameter differentiation, Taylor integral
remainder and implicit-function calculus.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity. Prove equality of functions by evaluating both sides at an arbitrary
argument.
-/
theorem finite_cubicIntegral_normalized_jet {β : ℝ} (hβ : 0<β) (n : ℕ) (D : ℕ → ℝ → ℝ)
    (hc : ∀ j≤n+3,ContinuousOn (D j) (Icc 0 β))
    (hd : ∀ j<n+3,∀ t∈Icc 0 β,HasDerivWithinAt (D j) (D (j+1) t) (Icc 0 β) t)
    {j : ℕ} (hj : j≤n) {t : ℝ} (ht : t∈Icc 0 β) :
    iteratedDerivWithin j (cubicIntegral D 0) (Icc 0 β) t/(j.factorial:ℝ)=
      ∫ v in Icc (0:ℝ) 1,cubicWeight j v*(D (j+3) (t*v)/((j+3).factorial:ℝ)) := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  rw [finite_cubicIntegral_iterated hβ n D hc hd j hj ht,cubicIntegral,← integral_div]
  congr 1
  funext v
  unfold cubicWeight
  have hf : ((j+3).factorial:ℝ)=
      ((j+3:ℕ):ℝ)*((j+2:ℕ):ℝ)*((j+1:ℕ):ℝ)*(j.factorial:ℝ) := by
    simp only [show j+3=(j+2)+1 by omega,show j+2=(j+1)+1 by omega,Nat.factorial_succ,Nat.cast_mul]
    ring
  rw [hf]
  field_simp

 /--
The precise assertion is `iteratedDerivWithin j (cubicIntegral D 0) (Icc 0 β)
0/(j.factorial:ℝ)= D (j+3) 0/((j+3).factorial:ℝ)`.

Use: `«2610.05164v2».Calculus.cubic_taylor_enclosure` uses this identity to establish the
identity stated in that declaration.

Article: 2610.05164v2, Lemma 22 via `«2610.05164v2».Calculus.removing_cubic_zero`.

Source: mathlib, Mathlib.Analysis.Calculus — parameter differentiation, Taylor integral
remainder and implicit-function calculus.

Proof: Use the identities/estimates
`«2610.05164v2».Calculus.finite_cubicIntegral_normalized_jet`,
`«2610.05164v2».Calculus.cubicWeight_integral` with the arguments shown in the proof.
-/
theorem finite_cubicIntegral_endpoint_jet {β : ℝ} (hβ : 0<β) (n : ℕ) (D : ℕ → ℝ → ℝ)
    (hc : ∀ j≤n+3,ContinuousOn (D j) (Icc 0 β))
    (hd : ∀ j<n+3,∀ t∈Icc 0 β,HasDerivWithinAt (D j) (D (j+1) t) (Icc 0 β) t)
    {j : ℕ} (hj : j≤n) :
    iteratedDerivWithin j (cubicIntegral D 0) (Icc 0 β) 0/(j.factorial:ℝ)=
      D (j+3) 0/((j+3).factorial:ℝ) := by
  rw [finite_cubicIntegral_normalized_jet hβ n D hc hd hj ⟨le_rfl,hβ.le⟩]
  simp only [zero_mul,integral_mul_const,cubicWeight_integral,one_mul]

 /--
Membership in the specified domain/enclosure: `iteratedDerivWithin j (cubicIntegral D 0) (Icc 0
β) t/(j.factorial:ℝ)∈Icc L U`.

Use: `«2610.05164v2».Calculus.cubic_taylor_enclosure` uses this assertion to establish the
identity stated in that declaration.

Article: 2610.05164v2, Lemma 22 via `«2610.05164v2».Calculus.removing_cubic_zero`.

Source: mathlib, Mathlib.Analysis.Calculus — parameter differentiation, Taylor integral
remainder and implicit-function calculus.

Proof: Use the identities/estimates
`«2610.05164v2».Calculus.finite_cubicIntegral_normalized_jet`,
`«2610.05164v2».Calculus.mul_unit_mem`, `«2610.05164v2».Calculus.cubic_jet_average_enclosure`
with the arguments shown in the proof.
-/
theorem finite_cubicIntegral_jet_enclosure {β : ℝ} (hβ : 0<β) (n : ℕ) (D : ℕ → ℝ → ℝ)
    (hc : ∀ j≤n+3,ContinuousOn (D j) (Icc 0 β))
    (hd : ∀ j<n+3,∀ t∈Icc 0 β,HasDerivWithinAt (D j) (D (j+1) t) (Icc 0 β) t)
    {j : ℕ} (hj : j≤n) {t L U : ℝ} (ht : t∈Icc 0 β)
    (hb : ∀ z∈Icc 0 t,D (j+3) z/((j+3).factorial:ℝ)∈Icc L U) :
    iteratedDerivWithin j (cubicIntegral D 0) (Icc 0 β) t/(j.factorial:ℝ)∈Icc L U := by
  -- Use the identities/estimates
  -- `«2610.05164v2».Calculus.finite_cubicIntegral_normalized_jet`,
  -- `«2610.05164v2».Calculus.mul_unit_mem`,
  -- `«2610.05164v2».Calculus.cubic_jet_average_enclosure` with the arguments shown in the
  -- proof.
  rw [finite_cubicIntegral_normalized_jet hβ n D hc hd hj ht]
  -- Establish continuity hcont before using the function at limits or in calculus arguments.
  have hcont : ContinuousOn (fun v => D (j+3) (t*v)/((j+3).factorial:ℝ)) (Icc (0:ℝ) 1) :=
    ((hc (j+3) (by omega)).comp (continuousOn_const.mul continuousOn_id)
      (fun _ hv => mul_unit_mem ht hv)).div_const _
  apply cubic_jet_average_enclosure j hcont
  intro v hv
  exact hb (t*v) ⟨mul_nonneg ht.1 hv.1,mul_le_of_le_one_right ht.1 hv.2⟩

end
end «2610.05164v2».Calculus
