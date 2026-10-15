import «2610.05164v2».Numerics.StateJet
import «2610.05164v2».Numerics.JetRules

/-!
Article: 2610.05164v2, Lemma 24.
Bridge from actual multivariable jets to the first and second derivatives along a state segment.
Use: `«2610.05164v2».Numerics.StateJetOn.segment_derivatives` feeds
`«2610.05164v2».Numerics.StateJetOn.segment_taylor_upper` (segment taylor upper).
Proof chain: `«2610.05164v2».Numerics.StateJetOn.segment_taylor_upper` — 2610.05164v2, Lemma 24;
Actual multivariable segment, state and time Taylor/concavity upper bounds.
-/
namespace «2610.05164v2».Numerics
noncomputable section
open Set
set_option autoImplicit false
set_option maxHeartbeats 1000000

/--
Establishes the uniform, quantified assertion `∀ t∈Icc (0:ℝ) 1, normalizedWithin (fun t =>
F.value (c+t • v)) (Icc (0:ℝ) 1) 1 t= ∑ i,F.gradient (c+t • v) i*v i ∧ 2*normalizedWithin (fun
t => F.value (c+t • v)) (Icc (0:ℝ) 1) 2 t= ∑ i,∑ j,F.hessian (c+t • v) i j*v i*v j`.

Use: `«2610.05164v2».Numerics.StateJetOn.segment_taylor_upper` uses this identity to establish
the stated quantitative bound `F.value (c+v)≤β+(∑ i,F.gradient c i*v i)+H/2`.

Article: 2610.05164v2, Lemma 24 via `«2610.05164v2».Numerics.StateJetOn.segment_taylor_upper`.

Proof: Identify the summands/integrands on their required domain before replacing the sum or
integral.
-/
theorem StateJetOn.segment_derivatives {d : ℕ} {s : Set (Fin d → ℝ)} (F : StateJetOn s)
    (c v : Fin d → ℝ) (hseg : ∀ t∈Icc (0:ℝ) 1,c+t • v∈s) :
    ∀ t∈Icc (0:ℝ) 1,
      normalizedWithin (fun t => F.value (c+t • v)) (Icc (0:ℝ) 1) 1 t=
        ∑ i,F.gradient (c+t • v) i*v i ∧
      2*normalizedWithin (fun t => F.value (c+t • v)) (Icc (0:ℝ) 1) 2 t=
        ∑ i,∑ j,F.hessian (c+t • v) i j*v i*v j := by
  -- Identify the summands/integrands on their required domain before replacing the sum or
  -- integral.
  let p := fun t : ℝ => c+t • v
  let g := fun t : ℝ => ∑ i,F.gradient (p t) i*v i
  have hp : ∀ t : ℝ,HasDerivWithinAt p v (Icc (0:ℝ) 1) t := by
    intro t
    convert ((hasDerivAt_const t c).add ((hasDerivAt_id t).smul_const v)).hasDerivWithinAt using 1
    · rfl
    · simp
  have hf : ∀ t∈Icc (0:ℝ) 1,HasDerivWithinAt (fun t => F.value (p t)) (g t) (Icc (0:ℝ) 1) t := by
    intro t ht
    convert! (F.value_derivative (p t) (hseg t ht)).comp_hasDerivWithinAt t (hp t) hseg using 1
    exact (gradientMap_apply (F.gradient (p t)) v).symm
  have hg : ∀ t∈Icc (0:ℝ) 1,HasDerivWithinAt g
      (∑ i,∑ j,F.hessian (p t) i j*v i*v j) (Icc (0:ℝ) 1) t := by
    intro t ht
    have hgi : ∀ i : Fin d,HasDerivWithinAt (fun t => F.gradient (p t) i*v i)
        ((∑ j,F.hessian (p t) i j*v j)*v i) (Icc (0:ℝ) 1) t := by
      intro i
      convert! ((F.gradient_derivative (p t) (hseg t ht) i).comp_hasDerivWithinAt t (hp t) hseg).mul_const (v i) using 1
      rw [gradientMap_apply]
    have hsum := HasDerivWithinAt.fun_sum (u := Finset.univ) (fun i _ => hgi i)
    convert! hsum using 1
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hs : UniqueDiffOn ℝ (Icc (0:ℝ) 1) := uniqueDiffOn_Icc (by norm_num)
  have heq : EqOn (derivWithin (fun t => F.value (p t)) (Icc (0:ℝ) 1)) g (Icc (0:ℝ) 1) :=
    fun t ht => (hf t ht).derivWithin (hs t ht)
  intro t ht
  constructor
  · simpa only [normalizedWithin,iteratedDerivWithin_one,Nat.factorial_one,Nat.cast_one,div_one] using heq ht
  · rw [show (2:ℝ)=((1:ℕ):ℝ)+1 by norm_num,← normalizedWithin_deriv,
      normalizedWithin_congr heq 1 ht]
    simpa only [normalizedWithin,iteratedDerivWithin_one,Nat.factorial_one,Nat.cast_one,div_one] using
      (hg t ht).derivWithin (hs t ht)

end
end «2610.05164v2».Numerics
