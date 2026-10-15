import «2610.05164v2».Numerics.JetRules
import «2610.05164v2».Calculus.FiniteTaylor

/-!
Article: 2610.05164v2, Lemma 21.
Forward Taylor bounds with the actual one-sided endpoint jets.
Use: `«2610.05164v2».Numerics.forward_taylor_bound` feeds
`«2610.05164v2».Numerics.riccati_taylor_propagation` (riccati taylor propagation).
Proof chain: `«2610.05164v2».Numerics.riccati_taylor_propagation` — 2610.05164v2, Lemma 21;
Validated signed-slope flow: existence, uniqueness and Taylor propagation.
-/
namespace «2610.05164v2».Numerics
noncomputable section
open Set Real
set_option autoImplicit false
set_option maxHeartbeats 1000000

/--
Constructs witnesses with the exact properties `∃ ξ∈Ioo (0:ℝ) v,f (a+v)- (∑ j∈Finset.range
(N+1),normalizedWithin f (Icc a (a+h)) j a*v^j)= normalizedWithin f (Icc a (a+h)) (N+1)
(a+ξ)*v^(N+1)`.

Use: `«2610.05164v2».Numerics.forward_taylor_bound` uses this identity to establish the stated
quantitative bound `|f (a+v)-∑ j∈Finset.range (N+1),normalizedWithin f (Icc a (a+h)) j a*v^j|
≤R*v^(N+1)`.

Article: 2610.05164v2, Lemma 21 via `«2610.05164v2».Numerics.riccati_taylor_propagation`.

Proof: Identify the summands/integrands on their required domain before replacing the sum or
integral.
-/
theorem forward_taylor_remainder {f : ℝ → ℝ} {a h v : ℝ} (N : ℕ)
    (hh : 0<h) (hv : v∈Ioc (0:ℝ) h)
    (hf : ContDiffOn ℝ (N+1) f (Icc a (a+h))) :
    ∃ ξ∈Ioo (0:ℝ) v,f (a+v)-
      (∑ j∈Finset.range (N+1),normalizedWithin f (Icc a (a+h)) j a*v^j)=
        normalizedWithin f (Icc a (a+h)) (N+1) (a+ξ)*v^(N+1) := by
  -- Identify the summands/integrands on their required domain before replacing the sum or
  -- integral.
  let S := Icc a (a+h)
  let F := fun j t => iteratedDerivWithin j f S (a+t)
  have hs : UniqueDiffOn ℝ S := uniqueDiffOn_Icc (by linarith)
  have hm : MapsTo (fun t : ℝ => a+t) (Icc (0:ℝ) h) S := by
    intro t ht
    exact ⟨by linarith [ht.1],by linarith [ht.2]⟩
  have hc : ∀ j≤N+1,ContinuousOn (F j) (Icc (0:ℝ) h) := by
    intro j hj
    exact (hf.continuousOn_iteratedDerivWithin (by exact_mod_cast hj) hs).comp
      (continuousOn_const.add continuousOn_id) hm
  have hd : ∀ j<N+1,∀ t∈Icc (0:ℝ) h,
      HasDerivWithinAt (F j) (F (j+1) t) (Icc (0:ℝ) h) t := by
    intro j hj t ht
    have hjd := hf.differentiableOn_iteratedDerivWithin (by exact_mod_cast hj) hs (a+t) (hm ht)
    have he : HasDerivWithinAt (iteratedDerivWithin j f S)
        (iteratedDerivWithin (j+1) f S (a+t)) S (a+t) := by
      simpa only [iteratedDerivWithin_succ] using hjd.hasDerivWithinAt
    simpa only [F,Function.comp_def,mul_one] using he.comp t
      ((hasDerivWithinAt_id t (Icc (0:ℝ) h)).const_add a) hm
  obtain ⟨ξ,hξ,he⟩ := Calculus.finite_chain_taylor (N+1) F hc hd (j := 0) (n := N)
    (by omega) hv
  have hpoly : (∑ j∈Finset.range (N+1),F (0+j) 0*v^j/(j.factorial:ℝ))=
      ∑ j∈Finset.range (N+1),normalizedWithin f S j a*v^j := by
    apply Finset.sum_congr rfl
    intro j _
    simp only [F,zero_add,add_zero,normalizedWithin]
    ring
  rw [hpoly] at he
  have he' : f (a+v)-(∑ j∈Finset.range (N+1),normalizedWithin f S j a*v^j)=
      normalizedWithin f S (N+1) (a+ξ)*v^(N+1) := by
    dsimp [F] at he
    simp only [zero_add,iteratedDerivWithin_zero] at he
    dsimp [normalizedWithin] at he ⊢
    linear_combination he
  exact ⟨ξ,hξ,he'⟩

/--
The stated quantitative bound `|f (a+v)-∑ j∈Finset.range (N+1),normalizedWithin f (Icc a (a+h))
j a*v^j| ≤R*v^(N+1)`.

Use: `«2610.05164v2».Numerics.riccati_taylor_propagation` uses this bound to establish the
stated quantitative bound `|y (a+v)-∑ j∈Finset.range (N+1),normalizedWithin z (Icc a (a+h)) j
a*v^j| ≤R*v^(N+1)+r*exp (L*v)`.

Article: 2610.05164v2, Lemma 21 via `«2610.05164v2».Numerics.riccati_taylor_propagation`.

Proof: Use the identities/estimates `«2610.05164v2».Numerics.forward_taylor_remainder` with the
arguments shown in the proof.
-/
theorem forward_taylor_bound {f : ℝ → ℝ} {a h R v : ℝ} (N : ℕ)
    (hh : 0<h) (hv : v∈Icc (0:ℝ) h)
    (hf : ContDiffOn ℝ (N+1) f (Icc a (a+h)))
    (hR : ∀ t∈Icc a (a+h),|normalizedWithin f (Icc a (a+h)) (N+1) t|≤R) :
    |f (a+v)-∑ j∈Finset.range (N+1),normalizedWithin f (Icc a (a+h)) j a*v^j|
      ≤R*v^(N+1) := by
  -- Use the identities/estimates `«2610.05164v2».Numerics.forward_taylor_remainder` with the
  -- arguments shown in the proof.
  rcases eq_or_lt_of_le hv.1 with hzero | hvpos
  · subst v
    have he : (∑ j∈Finset.range (N+1),normalizedWithin f (Icc a (a+h)) j a*(0:ℝ)^j)=f a := by
      rw [Finset.sum_eq_single 0]
      · simp
      · intro j _ hj
        simp [zero_pow hj]
      · simp
    simp [he]
  obtain ⟨ξ,hξ,he⟩ := forward_taylor_remainder N hh ⟨hvpos,hv.2⟩ hf
  rw [he,abs_mul,abs_pow,abs_of_nonneg hv.1]
  exact mul_le_mul_of_nonneg_right (hR (a+ξ)
    ⟨by linarith [hξ.1],by linarith [hξ.2,hv.2]⟩) (pow_nonneg hv.1 _)

end
end «2610.05164v2».Numerics
