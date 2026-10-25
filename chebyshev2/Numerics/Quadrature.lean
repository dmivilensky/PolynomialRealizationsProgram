import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Tactic

/-!
Article: chebyshev2, Lemma 20.
Sharp quadrature error and its bridge to the actual normalized derivatives of a function smooth on
the closed integration interval.
Use: `chebyshev2.Numerics.quadrature_taylor_even` feeds
`chebyshev2.Numerics.quadratureCheck_sound` (quadrature Check sound).
-/
namespace chebyshev2.Numerics
noncomputable section
open Set MeasureTheory intervalIntegral
set_option autoImplicit false

 /--
Exact identity `(∫ t in c-h..c+h,|t-c|^N)=2*h^(N+1)/(N+1)`.

Use: `chebyshev2.Numerics.quadrature_error` rewrites with this identity to establish the
stated quantitative bound `|(∫ t in c-h..c+h,f t)-(∫ t in c-h..c+h,p t)|≤2*M*h^(N+1)/(N+1)`.

Article: chebyshev2, Lemma 20 via `chebyshev2.Numerics.quadrature_taylor`.

Proof: Expand/rewrite the named definitions and identities appearing in the tactic block; the
remaining goal is a direct simplification or algebraic consequence.
-/
theorem integral_abs_center_pow (c h : ℝ) (N : ℕ) (hh : 0≤h) :
    (∫ t in c-h..c+h,|t-c|^N)=2*h^(N+1)/(N+1) := by
  -- Expand/rewrite the named definitions and identities appearing in the tactic block; the
  -- remaining goal is a direct simplification or algebraic consequence.
  have hright : (∫ t in (0:ℝ)..h,|t|^N)=h^(N+1)/(N+1) := by
    calc
      _=∫ t in (0:ℝ)..h,t^N := by
        apply integral_congr
        intro t ht
        rw [uIcc_of_le hh] at ht
        simp only [abs_of_nonneg ht.1]
      _=_ := by simp
  have hleft : (∫ t in -h..(0:ℝ),|t|^N)=h^(N+1)/(N+1) := by
    have he := integral_comp_neg (a := (0:ℝ)) (b := h) (fun t : ℝ => |t|^N)
    simp only [abs_neg,neg_zero] at he
    rw [← he,hright]
  -- Establish continuity hc before using the function at limits or in calculus arguments.
  have hc : Continuous (fun t : ℝ => |t|^N) := continuous_abs.pow N
  calc
    _=∫ t in -h..h,|t|^N := by
      simpa only [show c-h-c= -h by ring,show c+h-c=h by ring] using
        integral_comp_sub_right (a := c-h) (b := c+h) (fun t : ℝ => |t|^N) c
    _=(∫ t in -h..(0:ℝ),|t|^N)+(∫ t in (0:ℝ)..h,|t|^N) :=
      (integral_add_adjacent_intervals (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)).symm
    _=_ := by rw [hleft,hright];ring

 /--
The stated quantitative bound `|(∫ t in c-h..c+h,f t)-(∫ t in c-h..c+h,p
t)|≤2*M*h^(N+1)/(N+1)`.

Use: `chebyshev2.Numerics.quadrature_taylor` uses this bound to establish the stated
quantitative bound `|(∫ t in c-h..c+h,f t)- ∑ j∈Finset.range (n+1),normalizedDerivative f j
c*(h^(j+1)-(-h)^(j+1))/(j+1)| ≤2*M*h^(n+2)/(n+2)`.

Article: chebyshev2, Lemma 20 via `chebyshev2.Numerics.quadrature_taylor`.

Proof: Use the identities/estimates `chebyshev2.Numerics.integral_abs_center_pow` with the
arguments shown in the proof.
-/
theorem quadrature_error {f p : ℝ → ℝ} {c h M : ℝ} (N : ℕ) (hh : 0≤h)
    (hf : IntervalIntegrable f volume (c-h) (c+h))
    (hp : IntervalIntegrable p volume (c-h) (c+h))
    (hR : ∀ t∈Icc (c-h) (c+h),|f t-p t|≤M*|t-c|^N) :
    |(∫ t in c-h..c+h,f t)-(∫ t in c-h..c+h,p t)|≤2*M*h^(N+1)/(N+1) := by
  -- Use the identities/estimates `chebyshev2.Numerics.integral_abs_center_pow` with the
  -- arguments shown in the proof.
  have hb : IntervalIntegrable (fun t : ℝ => M*|t-c|^N) volume (c-h) (c+h) := by
    exact (continuous_const.mul ((continuous_id.sub continuous_const).abs.pow N)).intervalIntegrable _ _
  have he := norm_integral_le_of_norm_le (f := fun t => f t-p t) (g := fun t => M*|t-c|^N)
    (by linarith : c-h≤c+h)
    (Filter.Eventually.of_forall (fun t ht => by simpa only [Real.norm_eq_abs] using hR t ⟨ht.1.le,ht.2⟩)) hb
  rw [integral_sub hf hp,Real.norm_eq_abs,intervalIntegral.integral_const_mul,integral_abs_center_pow c h N hh] at he
  convert he using 1
  ring

 /--
Exact identity `(∫ t in c-h..c+h,(t-c)^j)=(h^(j+1)-(-h)^(j+1))/(j+1)`.

Use: `chebyshev2.Numerics.integral_center_polynomial` rewrites with this identity to
establish membership in the specified domain/enclosure: `(∫ t in c-h..c+h,∑ j∈Finset.range N,a
j*(t-c)^j)= ∑ j∈Finset.range N,a j*(h^(j+1)-(-h)^(j+1))/(j+1)`.

Article: chebyshev2, Lemma 20 via `chebyshev2.Numerics.quadrature_taylor`.

Proof: Expand/rewrite the named definitions and identities appearing in the tactic block; the
remaining goal is a direct simplification or algebraic consequence.
-/
theorem integral_center_monomial (c h : ℝ) (j : ℕ) :
    (∫ t in c-h..c+h,(t-c)^j)=(h^(j+1)-(-h)^(j+1))/(j+1) := by
  calc
    _=∫ t in -h..h,t^j := by
      simpa only [show c-h-c= -h by ring,show c+h-c=h by ring] using
        integral_comp_sub_right (a := c-h) (b := c+h) (fun t : ℝ => t^j) c
    _=_ := integral_pow j

 /--
Membership in the specified domain/enclosure: `(∫ t in c-h..c+h,∑ j∈Finset.range N,a
j*(t-c)^j)= ∑ j∈Finset.range N,a j*(h^(j+1)-(-h)^(j+1))/(j+1)`.

Use: `chebyshev2.Numerics.quadrature_taylor` uses this identity to establish the stated
quantitative bound `|(∫ t in c-h..c+h,f t)- ∑ j∈Finset.range (n+1),normalizedDerivative f j
c*(h^(j+1)-(-h)^(j+1))/(j+1)| ≤2*M*h^(n+2)/(n+2)`.

Article: chebyshev2, Lemma 20 via `chebyshev2.Numerics.quadrature_taylor`.

Proof: Identify the summands/integrands on their required domain before replacing the sum or
integral.
-/
theorem integral_center_polynomial (a : ℕ → ℝ) (N : ℕ) (c h : ℝ) :
    (∫ t in c-h..c+h,∑ j∈Finset.range N,a j*(t-c)^j)=
      ∑ j∈Finset.range N,a j*(h^(j+1)-(-h)^(j+1))/(j+1) := by
  -- Identify the summands/integrands on their required domain before replacing the sum or
  -- integral.
  have hi : ∀ j∈Finset.range N,IntervalIntegrable (fun t : ℝ => a j*(t-c)^j) volume (c-h) (c+h) := by
    intro j _
    apply Continuous.intervalIntegrable
    fun_prop
  rw [intervalIntegral.integral_finsetSum hi]
  apply Finset.sum_congr rfl
  intro j _
  rw [intervalIntegral.integral_const_mul,integral_center_monomial]
  ring

/--
Actual normalized derivatives, not coefficients supplied by an exporter.

Use: `chebyshev2.Numerics.quadrature_taylor` rewrites with this definition to establish the
stated quantitative bound `|(∫ t in c-h..c+h,f t)- ∑ j∈Finset.range (n+1),normalizedDerivative
f j c*(h^(j+1)-(-h)^(j+1))/(j+1)| ≤2*M*h^(n+2)/(n+2)`.

Article: chebyshev2, Lemma 20 via `chebyshev2.Numerics.quadrature_taylor`.
-/
def normalizedDerivative (f : ℝ → ℝ) (j : ℕ) (x : ℝ) : ℝ :=
  iteratedDeriv j f x/(j.factorial:ℝ)

 /--
The stated quantitative bound `|(∫ t in c-h..c+h,f t)- ∑ j∈Finset.range
(n+1),normalizedDerivative f j c*(h^(j+1)-(-h)^(j+1))/(j+1)| ≤2*M*h^(n+2)/(n+2)`.

Use: `chebyshev2.Numerics.quadrature_taylor_even` uses this bound to establish the stated
quantitative bound `|(∫ t in c-h..c+h,f t)- ∑ j∈Finset.range (n+1) with Even
j,2*h^(j+1)/(j+1)*normalizedDerivative f j c| ≤2*M*h^(n+2)/(n+2)`.

Article: chebyshev2, Lemma 20.

Proof: Separate `c=x` from its negation; prove the goal under each of these mutually exclusive
hypotheses. Identify the summands/integrands on their required domain before replacing the sum
or integral. Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem quadrature_taylor {f : ℝ → ℝ} {c h M : ℝ} (n : ℕ) (hh : 0≤h)
    (hf : ContDiffOn ℝ (n+1) f (Icc (c-h) (c+h)))
    (hM : ∀ t∈Icc (c-h) (c+h),|normalizedDerivative f (n+1) t|≤M) :
    |(∫ t in c-h..c+h,f t)-
      ∑ j∈Finset.range (n+1),normalizedDerivative f j c*(h^(j+1)-(-h)^(j+1))/(j+1)|
      ≤2*M*h^(n+2)/(n+2) := by
  -- Separate `c=x` from its negation; prove the goal under each of these mutually exclusive
  -- hypotheses.
  rcases eq_or_lt_of_le hh with he | hh
  · have hz : h=0 := he.symm
    simp [hz]
  have hc : c∈Icc (c-h) (c+h) := ⟨by linarith,by linarith⟩
  have hca : ContDiffAt ℝ (n+1) f c := hf.contDiffAt (Icc_mem_nhds (by linarith) (by linarith))
  let p := taylorWithinEval f n univ c
  have hpoly : ∀ x,p x=∑ j∈Finset.range (n+1),normalizedDerivative f j c*(x-c)^j := by
    intro x
    rw [show p x=taylorWithinEval f n univ c x from rfl,taylor_within_apply]
    apply Finset.sum_congr rfl
    intro j _
    simp only [iteratedDerivWithin_univ,smul_eq_mul,normalizedDerivative,div_eq_mul_inv]
    ring
  -- Establish continuity hp before using the function at limits or in calculus arguments.
  have hp : Continuous p := by
    have he : p=fun x => ∑ j∈Finset.range (n+1),normalizedDerivative f j c*(x-c)^j := funext hpoly
    rw [he]
    fun_prop
  have hR : ∀ x∈Icc (c-h) (c+h),|f x-p x|≤M*|x-c|^(n+1) := by
    intro x hx
    by_cases hcx : c=x
    · subst x
      simp [p]
    have hsub : uIcc c x⊆Icc (c-h) (c+h) := by
      intro z hz
      exact ⟨(le_min hc.1 hx.1).trans hz.1,hz.2.trans (max_le hc.2 hx.2)⟩
    have ht : taylorWithinEval f n (uIcc c x) c x=p x := by
      rw [show p x=taylorWithinEval f n univ c x from rfl,taylor_within_apply,taylor_within_apply]
      apply Finset.sum_congr rfl
      intro j hj
      rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc hcx)
        (hca.of_le (by exact_mod_cast (Nat.le_of_lt (Finset.mem_range.mp hj)))) left_mem_uIcc,
        iteratedDerivWithin_univ]
    obtain ⟨ξ,hξ,he⟩ := taylor_mean_remainder_lagrange_iteratedDeriv hcx (hf.mono hsub)
    have hξc : ξ∈Icc (c-h) (c+h) := hsub ⟨hξ.1.le,hξ.2.le⟩
    calc
      |f x-p x|=|normalizedDerivative f (n+1) ξ| *|x-c|^(n+1) := by
        rw [← ht,he]
        simp only [normalizedDerivative,abs_div,abs_mul,abs_pow,Nat.abs_cast]
        ring
      _≤M*|x-c|^(n+1) := mul_le_mul_of_nonneg_right (hM ξ hξc) (by positivity)
  have hfin : IntervalIntegrable f volume (c-h) (c+h) := by
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le (by linarith : c-h≤c+h)] using hf.continuousOn
  have he := quadrature_error (n+1) hh.le hfin (hp.intervalIntegrable _ _) hR
  have hi : (∫ t in c-h..c+h,p t)=
      ∑ j∈Finset.range (n+1),normalizedDerivative f j c*(h^(j+1)-(-h)^(j+1))/(j+1) := by
    rw [intervalIntegral.integral_congr (fun x _ => hpoly x)]
    exact integral_center_polynomial (normalizedDerivative f · c) (n+1) c h
  rw [hi] at he
  have hcast : ((n+1:ℕ):ℝ)+1=(n:ℝ)+2 := by push_cast;ring
  simpa only [show n+1+1=n+2 by omega,hcast] using he

 /--
Exact identity `(h^(j+1)-(-h)^(j+1))/(j+1)=if Even j then 2*h^(j+1)/(j+1) else 0`.

Use: `chebyshev2.Numerics.quadrature_taylor_even` rewrites with this identity to establish
the stated quantitative bound `|(∫ t in c-h..c+h,f t)- ∑ j∈Finset.range (n+1) with Even
j,2*h^(j+1)/(j+1)*normalizedDerivative f j c| ≤2*M*h^(n+2)/(n+2)`.

Article: chebyshev2, Lemma 20 via `chebyshev2.Numerics.quadrature_taylor_even`.

Proof: Separate `Even j` from its negation; prove the goal under each of these mutually
exclusive hypotheses.
-/
theorem centered_monomial_weight (h : ℝ) (j : ℕ) :
    (h^(j+1)-(-h)^(j+1))/(j+1)=if Even j then 2*h^(j+1)/(j+1) else 0 := by
  by_cases hj : Even j
  · simp only [ite_eq_left hj,pow_succ,hj.neg_pow]
    ring
  · have ho : Odd j := Nat.not_even_iff_odd.mp hj
    simp only [ite_eq_right hj,pow_succ,ho.neg_pow]
    ring

/--
Lemma 20 in the article's even-index form, with N=n+1.

The stated quantitative bound `|(∫ t in c-h..c+h,f t)- ∑ j∈Finset.range (n+1) with Even
j,2*h^(j+1)/(j+1)*normalizedDerivative f j c| ≤2*M*h^(n+2)/(n+2)`.

Use: `chebyshev2.Numerics.quadratureCheck_sound` uses this bound to establish membership in
the specified domain/enclosure: `(∫ t in c-h..c+h,f t)∈output`.

Article: chebyshev2, Lemma 20.

Proof: Identify the summands/integrands on their required domain before replacing the sum or
integral.
-/
theorem quadrature_taylor_even {f : ℝ → ℝ} {c h M : ℝ} (n : ℕ) (hh : 0≤h)
    (hf : ContDiffOn ℝ (n+1) f (Icc (c-h) (c+h)))
    (hM : ∀ t∈Icc (c-h) (c+h),|normalizedDerivative f (n+1) t|≤M) :
    |(∫ t in c-h..c+h,f t)-
      ∑ j∈Finset.range (n+1) with Even j,2*h^(j+1)/(j+1)*normalizedDerivative f j c|
      ≤2*M*h^(n+2)/(n+2) := by
  -- Identify the summands/integrands on their required domain before replacing the sum or
  -- integral.
  have he : (∑ j∈Finset.range (n+1),normalizedDerivative f j c*(h^(j+1)-(-h)^(j+1))/(j+1))=
      ∑ j∈Finset.range (n+1) with Even j,2*h^(j+1)/(j+1)*normalizedDerivative f j c := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro j _
    rw [mul_div_assoc,centered_monomial_weight]
    split_ifs <;> ring
  rw [← he]
  exact quadrature_taylor n hh hf hM

end
end chebyshev2.Numerics
