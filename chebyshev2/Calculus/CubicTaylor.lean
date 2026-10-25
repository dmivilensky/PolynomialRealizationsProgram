import chebyshev2.Calculus.FiniteTaylor
import Mathlib.Data.Nat.Choose.Cast

/-!
Article: chebyshev2, Lemma 22.
Lemma 22's normalized Taylor enclosure, including the cubic endpoint.
Use: `chebyshev2.Calculus.cubic_taylor_enclosure` feeds
`chebyshev2.Calculus.removing_cubic_zero` (removing cubic zero).
Proof chain: `chebyshev2.Calculus.removing_cubic_zero` — chebyshev2, Lemma 22; Removal of a
cubic zero at the available finite differentiability order.
Source: mathlib, Mathlib.Analysis.Calculus — parameter differentiation, Taylor integral remainder
and implicit-function calculus. The needed form is proved here.
-/
namespace chebyshev2.Calculus
noncomputable section
open Set MeasureTheory Real
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

 /--
Constructs witnesses with the exact properties `∃ r∈Icc L U, iteratedDerivWithin j
(cubicIntegral D 0) (Icc 0 β) t/(j.factorial:ℝ)= (∑ l∈Finset.range (N-j+1),((j+l).choose j:ℝ)*
(D (j+l+3) 0/((j+l+3).factorial:ℝ))*t^l)+ ((N+1).choose j:ℝ)*t^(N+1-j)*r`.

Use: `chebyshev2.Calculus.removing_cubic_zero` uses this identity to establish the identity
stated in that declaration.

Article: chebyshev2, Lemma 22 via `chebyshev2.Calculus.removing_cubic_zero`.

Source: mathlib, Mathlib.Analysis.Calculus — parameter differentiation, Taylor integral
remainder and implicit-function calculus.

Proof: Separate `t=0` from its negation; prove the goal under each of these mutually exclusive
hypotheses. Identify the summands/integrands on their required domain before replacing the sum
or integral. Clear the denominators using the available nonzero hypotheses, then verify the
remaining algebraic identity.
-/
theorem cubic_taylor_enclosure {β : ℝ} (hβ : 0<β) (N : ℕ) (D : ℕ → ℝ → ℝ)
    (hc : ∀ l≤N+4,ContinuousOn (D l) (Icc 0 β))
    (hd : ∀ l<N+4,∀ t∈Icc 0 β,HasDerivWithinAt (D l) (D (l+1) t) (Icc 0 β) t)
    {j : ℕ} (hj : j≤N) {t L U : ℝ} (ht : t∈Icc 0 β)
    (hb : ∀ z∈Icc 0 β,D (N+4) z/((N+4).factorial:ℝ)∈Icc L U) :
    ∃ r∈Icc L U,
      iteratedDerivWithin j (cubicIntegral D 0) (Icc 0 β) t/(j.factorial:ℝ)=
        (∑ l∈Finset.range (N-j+1),((j+l).choose j:ℝ)*
          (D (j+l+3) 0/((j+l+3).factorial:ℝ))*t^l)+
        ((N+1).choose j:ℝ)*t^(N+1-j)*r := by
  -- Separate `t=0` from its negation; prove the goal under each of these mutually exclusive
  -- hypotheses.
  have hc' : ∀ l≤N+1,ContinuousOn (cubicIntegral D l) (Icc 0 β) := by
    intro l hl
    exact continuousOn_compact_integral (finite_cubic_integrand_continuous D l (hc (l+3) (by omega)))
  have hd' : ∀ l<N+1,∀ t∈Icc 0 β,
      HasDerivWithinAt (cubicIntegral D l) (cubicIntegral D (l+1) t) (Icc 0 β) t := by
    intro l hl t ht
    exact finite_cubicIntegral_derivative hβ D l (hc (l+3) (by omega)) (hc (l+4) (by omega))
      (by simpa only [show l+3+1=l+4 by omega] using hd (l+3) (by omega)) ht
  have hjet (l : ℕ) (hl : l≤N+1) {z : ℝ} (hz : z∈Icc 0 β) :
      iteratedDerivWithin l (cubicIntegral D 0) (Icc 0 β) z=cubicIntegral D l z :=
    finite_cubicIntegral_iterated hβ (N+1) D (by simpa using hc) (by simpa using hd) l hl hz
  have hend (l : ℕ) (hl : l≤N+1) :
      cubicIntegral D l 0/(l.factorial:ℝ)=D (l+3) 0/((l+3).factorial:ℝ) := by
    rw [← hjet l hl ⟨le_rfl,hβ.le⟩]
    exact finite_cubicIntegral_endpoint_jet hβ (N+1) D (by simpa using hc) (by simpa using hd) hl
  have hrem {z : ℝ} (hz : z∈Icc 0 β) :
      cubicIntegral D (N+1) z/((N+1).factorial:ℝ)∈Icc L U := by
    rw [← hjet (N+1) le_rfl hz]
    apply finite_cubicIntegral_jet_enclosure hβ (N+1) D (by simpa using hc) (by simpa using hd) le_rfl hz
    intro w hw
    simpa only [show N+1+3=N+4 by omega] using hb w ⟨hw.1,hw.2.trans hz.2⟩
  rw [hjet j (by omega) ht]
  by_cases hz : t=0
  · subst t
    refine ⟨cubicIntegral D (N+1) 0/((N+1).factorial:ℝ),hrem ⟨le_rfl,hβ.le⟩,?_⟩
    rw [hend j (by omega)]
    simp only [zero_pow (show N+1-j≠0 by omega),mul_zero,zero_mul,add_zero]
    rw [Finset.sum_eq_single 0]
    · simp
    · intro l _ hl
      simp [zero_pow hl]
    · intro h
      exact (h (by simp)).elim
  have hp : 0<t := lt_of_le_of_ne ht.1 (Ne.symm hz)
  obtain ⟨ξ,hξ,he⟩ := finite_chain_taylor (N+1) (cubicIntegral D) hc' hd'
    (j := j) (n := N-j) (by omega) ⟨hp,ht.2⟩
  have hξβ : ξ∈Icc 0 β := ⟨hξ.1.le,hξ.2.le.trans ht.2⟩
  refine ⟨cubicIntegral D (N+1) ξ/((N+1).factorial:ℝ),hrem hξβ,?_⟩
  rw [he,add_div,Finset.sum_div]
  congr 1
  · apply Finset.sum_congr rfl
    intro l hl
    have hlN : j+l≤N+1 := by have := Finset.mem_range.mp hl;omega
    rw [Nat.cast_add_choose ℝ,← hend (j+l) hlN]
    field_simp
  · have heq : j+(N-j)+1=N+1 := by omega
    rw [heq]
    have hn : N-j+1=N+1-j := by omega
    rw [hn,Nat.cast_choose ℝ (show j≤N+1 by omega)]
    field_simp

end
end chebyshev2.Calculus
