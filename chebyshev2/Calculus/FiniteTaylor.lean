import chebyshev2.Calculus.FiniteCubicJets
import Mathlib.Analysis.Calculus.Taylor

/-!
Article: chebyshev2, Lemma 22.
Finite derivative chains and Taylor remainders on a closed interval.
Use: `chebyshev2.Calculus.finite_chain_taylor` feeds
`chebyshev2.Numerics.forward_taylor_remainder` (forward taylor remainder).
Proof chain: `chebyshev2.Calculus.removing_cubic_zero` — chebyshev2, Lemma 22; Removal of a
cubic zero at the available finite differentiability order.
Source: mathlib, Mathlib.Analysis.Calculus — parameter differentiation, Taylor integral remainder
and implicit-function calculus. The needed form is proved here.
-/
namespace chebyshev2.Calculus
noncomputable section
open Set MeasureTheory Real
open scoped ContDiff
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

 /--
Establishes the uniform, quantified assertion `∀ n j : ℕ,j+n≤N → ContDiffOn ℝ n (F j) (Icc a
b)`.

Use: `chebyshev2.Calculus.finite_chain_taylor` uses this bound to establish constructs
witnesses with the exact properties `∃ ξ∈Ioo (0:ℝ) t,F j t= (∑ l∈Finset.range (n+1), F (j+l)
0*t^l/(l.factorial:ℝ))+ F (j+n+1) ξ*t^(n+1)/((n+1).factorial:ℝ)`.

Article: chebyshev2, Lemma 22 via `chebyshev2.Calculus.removing_cubic_zero`.

Source: mathlib, Mathlib.Analysis.Calculus — parameter differentiation, Taylor integral
remainder and implicit-function calculus.

Proof: Induct on `n`; the recursive step uses the previous-stage assertion.
-/
theorem finite_chain_smooth {a b : ℝ} (hab : a<b) (N : ℕ) (F : ℕ → ℝ → ℝ)
    (hc : ∀ j≤N,ContinuousOn (F j) (Icc a b))
    (hd : ∀ j<N,∀ t∈Icc a b,HasDerivWithinAt (F j) (F (j+1) t) (Icc a b) t) :
    ∀ n j : ℕ,j+n≤N → ContDiffOn ℝ n (F j) (Icc a b) := by
  -- Induct on `n`; the recursive step uses the previous-stage assertion.
  intro n
  induction n with
  | zero => intro j hj;exact contDiffOn_zero.mpr (hc j (by omega))
  | succ n ih =>
    intro j hj
    rw [show ((n+1:ℕ):ℕ∞ω)=(n:ℕ∞ω)+1 by simp,
      contDiffOn_succ_iff_derivWithin (uniqueDiffOn_Icc hab)]
    refine ⟨fun t ht => (hd j (by omega) t ht).differentiableWithinAt,by simp,?_⟩
    exact (ih (j+1) (by omega)).congr
      (fun t ht => (hd j (by omega) t ht).derivWithin (uniqueDiffOn_Icc hab t ht))

 /--
Establishes the uniform, quantified assertion `∀ n j : ℕ,j+n≤N → EqOn (iteratedDerivWithin n (F
j) (Icc a b)) (F (j+n)) (Icc a b)`.

Use: `chebyshev2.Calculus.finite_chain_taylor` rewrites with this bound to establish
constructs witnesses with the exact properties `∃ ξ∈Ioo (0:ℝ) t,F j t= (∑ l∈Finset.range (n+1),
F (j+l) 0*t^l/(l.factorial:ℝ))+ F (j+n+1) ξ*t^(n+1)/((n+1).factorial:ℝ)`.

Article: chebyshev2, Lemma 22 via `chebyshev2.Calculus.removing_cubic_zero`.

Source: mathlib, Mathlib.Analysis.Calculus — parameter differentiation, Taylor integral
remainder and implicit-function calculus.

Proof: Induct on `n`; the recursive step uses the previous-stage assertion.
-/
theorem finite_chain_iterated {a b : ℝ} (hab : a<b) (N : ℕ) (F : ℕ → ℝ → ℝ)
    (hd : ∀ j<N,∀ t∈Icc a b,HasDerivWithinAt (F j) (F (j+1) t) (Icc a b) t) :
    ∀ n j : ℕ,j+n≤N → EqOn (iteratedDerivWithin n (F j) (Icc a b)) (F (j+n)) (Icc a b) := by
  -- Induct on `n`; the recursive step uses the previous-stage assertion.
  intro n
  induction n with
  | zero => intro j _ t _;simp
  | succ n ih =>
    intro j hj t ht
    rw [iteratedDerivWithin_succ,derivWithin_congr (ih j (by omega)) (ih j (by omega) ht)]
    convert! (hd (j+n) (by omega) t ht).derivWithin (uniqueDiffOn_Icc hab t ht) using 1

 /--
Constructs witnesses with the exact properties `∃ ξ∈Ioo (0:ℝ) t,F j t= (∑ l∈Finset.range (n+1),
F (j+l) 0*t^l/(l.factorial:ℝ))+ F (j+n+1) ξ*t^(n+1)/((n+1).factorial:ℝ)`.

Use: `chebyshev2.Calculus.cubic_taylor_enclosure` uses this identity to establish the
identity stated in that declaration.

Article: chebyshev2, Lemma 22 via `chebyshev2.Calculus.removing_cubic_zero`.

Source: mathlib, Mathlib.Analysis.Calculus — parameter differentiation, Taylor integral
remainder and implicit-function calculus.

Proof: Identify the summands/integrands on their required domain before replacing the sum or
integral.
-/
theorem finite_chain_taylor {β : ℝ} (N : ℕ) (F : ℕ → ℝ → ℝ)
    (hc : ∀ j≤N,ContinuousOn (F j) (Icc 0 β))
    (hd : ∀ j<N,∀ t∈Icc 0 β,HasDerivWithinAt (F j) (F (j+1) t) (Icc 0 β) t)
    {j n : ℕ} (hjn : j+n+1≤N) {t : ℝ} (ht : t∈Ioc (0:ℝ) β) :
    ∃ ξ∈Ioo (0:ℝ) t,F j t=
      (∑ l∈Finset.range (n+1), F (j+l) 0*t^l/(l.factorial:ℝ))+
        F (j+n+1) ξ*t^(n+1)/((n+1).factorial:ℝ) := by
  -- Identify the summands/integrands on their required domain before replacing the sum or
  -- integral.
  have hsub : Icc (0:ℝ) t⊆Icc 0 β := Icc_subset_Icc le_rfl ht.2
  have hc' : ∀ l≤N,ContinuousOn (F l) (Icc (0:ℝ) t) := fun l hl => (hc l hl).mono hsub
  have hd' : ∀ l<N,∀ z∈Icc (0:ℝ) t,HasDerivWithinAt (F l) (F (l+1) z) (Icc 0 t) z :=
    fun l hl z hz => (hd l hl z (hsub hz)).mono hsub
  have hs := finite_chain_smooth ht.1 N F hc' hd' n j (by omega)
  have hdiff : DifferentiableOn ℝ (iteratedDerivWithin n (F j) (Icc (0:ℝ) t)) (Ioo 0 t) := by
    apply DifferentiableOn.congr (f := F (j+n))
    · intro z hz
      exact ((hd' (j+n) (by omega) z ⟨hz.1.le,hz.2.le⟩).hasDerivAt
        (Icc_mem_nhds hz.1 hz.2)).differentiableAt.differentiableWithinAt
    · intro z hz
      exact finite_chain_iterated ht.1 N F hd' n j (by omega) ⟨hz.1.le,hz.2.le⟩
  have hu : uIcc (0:ℝ) t=Icc 0 t := uIcc_of_le ht.1.le
  have huo : uIoo (0:ℝ) t=Ioo 0 t := by simp [uIoo,ht.1.le]
  obtain ⟨ξ,hξ,he⟩ := taylor_mean_remainder_lagrange (x₀ := 0) (x := t) ht.1.ne (by simpa only [hu] using hs)
    (by simpa only [hu,huo] using hdiff)
  rw [hu] at he
  rw [huo] at hξ
  rw [taylor_within_apply,finite_chain_iterated ht.1 N F hd' (n+1) j (by omega) ⟨hξ.1.le,hξ.2.le⟩] at he
  have hp : (∑ l∈Finset.range (n+1),((l.factorial:ℝ)⁻¹*(t-0)^l) •
      iteratedDerivWithin l (F j) (Icc 0 t) 0)=
      ∑ l∈Finset.range (n+1),F (j+l) 0*t^l/(l.factorial:ℝ) := by
    apply Finset.sum_congr rfl
    intro l hl
    rw [finite_chain_iterated ht.1 N F hd' l j (by have := Finset.mem_range.mp hl;omega) ⟨le_rfl,ht.1.le⟩]
    simp only [smul_eq_mul,sub_zero,div_eq_mul_inv]
    ring
  rw [hp] at he
  refine ⟨ξ,hξ,?_⟩
  simpa only [sub_zero,show j+(n+1)=j+n+1 by omega,add_comm] using (sub_eq_iff_eq_add.mp he)

end
end chebyshev2.Calculus
