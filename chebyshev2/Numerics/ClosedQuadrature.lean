import chebyshev2.Numerics.QuadratureCheck

/-!
Article: chebyshev2, Lemma 20.
`chebyshev2.Numerics.quadratureCheck_sound_closed` allows quadrature at closed endpoints using
within derivatives.
Interface: its result can discharge the corresponding enclosure premises of
`chebyshev2.Numerics.actualJetIntegralBox_sound_on`.
Proof chain: chebyshev2, Theorem 3.6, via the general enclosure rules of Appendix F.2. This is a
reusable analytic interface, not a concrete full-dual acceptance claim.
Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.
-/
namespace chebyshev2.Numerics
noncomputable section
open Set MeasureTheory intervalIntegral LeanCert.Core
set_option autoImplicit false
set_option maxHeartbeats 1000000
 /--
The stated quantitative bound `|(∫ t in c-h..c+h,f t)- ∑ j∈Finset.range (n+1),normalizedWithin
f (Icc (c-h) (c+h)) j c*(h^(j+1)-(-h)^(j+1))/(j+1)| ≤2*M*h^(n+2)/(n+2)`.

Use: `chebyshev2.Numerics.quadrature_taylor_even_closed` uses this bound to establish the
stated quantitative bound `|(∫ t in c-h..c+h,f t)- ∑ j∈Finset.range (n+1) with Even
j,2*h^(j+1)/(j+1)*normalizedWithin f (Icc (c-h) (c+h)) j c| ≤2*M*h^(n+2)/(n+2)`.

Article: chebyshev2, Lemma 20.

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.

Proof: Separate `c=x` from its negation; prove the goal under each of these mutually exclusive
hypotheses. Identify the summands/integrands on their required domain before replacing the sum
or integral. Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem quadrature_taylor_closed {f : ℝ → ℝ} {c h M : ℝ} (n : ℕ) (hh : 0≤h)
    (hf : ContDiffOn ℝ (n+1) f (Icc (c-h) (c+h)))
    (hM : ∀ t∈Icc (c-h) (c+h),|normalizedWithin f (Icc (c-h) (c+h)) (n+1) t|≤M) :
    |(∫ t in c-h..c+h,f t)-
      ∑ j∈Finset.range (n+1),normalizedWithin f (Icc (c-h) (c+h)) j c*(h^(j+1)-(-h)^(j+1))/(j+1)|
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
    have hξo : ξ∈Ioo (c-h) (c+h) := by
      rcases lt_or_gt_of_ne hcx with hleft | hright
      · rw [uIoo_of_lt hleft] at hξ
        exact ⟨by linarith [hξ.1],hξ.2.trans_le hx.2⟩
      · rw [uIoo_of_gt hright] at hξ
        exact ⟨hx.1.trans_lt hξ.1,by linarith [hξ.2]⟩
    have hξnorm : normalizedDerivative f (n+1) ξ=
        normalizedWithin f (Icc (c-h) (c+h)) (n+1) ξ := by
      rw [normalizedWithin,normalizedDerivative,
        iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc (by linarith))
          (hf.contDiffAt (Icc_mem_nhds hξo.1 hξo.2)) hξc]
    calc
      |f x-p x|=|normalizedDerivative f (n+1) ξ| *|x-c|^(n+1) := by
        rw [← ht,he]
        simp only [normalizedDerivative,abs_div,abs_mul,abs_pow,Nat.abs_cast]
        ring
      _≤M*|x-c|^(n+1) := mul_le_mul_of_nonneg_right (by rw [hξnorm];exact hM ξ hξc) (by positivity)
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
  have hcenter : ∀ j≤n,normalizedDerivative f j c=
      normalizedWithin f (Icc (c-h) (c+h)) j c := by
    intro j hj
    rw [normalizedWithin,normalizedDerivative,
      iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc (by linarith))
        (hca.of_le (by exact_mod_cast (show j≤n+1 by omega))) hc]
  have hsum : (∑ j∈Finset.range (n+1),normalizedDerivative f j c*(h^(j+1)-(-h)^(j+1))/(j+1))=
      ∑ j∈Finset.range (n+1),normalizedWithin f (Icc (c-h) (c+h)) j c*(h^(j+1)-(-h)^(j+1))/(j+1) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [hcenter j (by have := Finset.mem_range.mp hj;omega)]
  rw [hsum] at he
  simpa only [show n+1+1=n+2 by omega,hcast] using he

 /--
The stated quantitative bound `|(∫ t in c-h..c+h,f t)- ∑ j∈Finset.range (n+1) with Even
j,2*h^(j+1)/(j+1)*normalizedWithin f (Icc (c-h) (c+h)) j c| ≤2*M*h^(n+2)/(n+2)`.

Use: `chebyshev2.Numerics.quadratureCheck_sound_closed` uses this bound to establish
membership in the specified domain/enclosure: `(∫ t in c-h..c+h,f t)∈output`.

Article: chebyshev2, Lemma 20.

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.

Proof: Identify the summands/integrands on their required domain before replacing the sum or
integral.
-/
theorem quadrature_taylor_even_closed {f : ℝ → ℝ} {c h M : ℝ} (n : ℕ) (hh : 0≤h)
    (hf : ContDiffOn ℝ (n+1) f (Icc (c-h) (c+h)))
    (hM : ∀ t∈Icc (c-h) (c+h),|normalizedWithin f (Icc (c-h) (c+h)) (n+1) t|≤M) :
    |(∫ t in c-h..c+h,f t)-
      ∑ j∈Finset.range (n+1) with Even j,2*h^(j+1)/(j+1)*normalizedWithin f (Icc (c-h) (c+h)) j c|
      ≤2*M*h^(n+2)/(n+2) := by
  -- Identify the summands/integrands on their required domain before replacing the sum or
  -- integral.
  have he : (∑ j∈Finset.range (n+1),normalizedWithin f (Icc (c-h) (c+h)) j c*(h^(j+1)-(-h)^(j+1))/(j+1))=
      ∑ j∈Finset.range (n+1) with Even j,2*h^(j+1)/(j+1)*normalizedWithin f (Icc (c-h) (c+h)) j c := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro j _
    rw [mul_div_assoc,centered_monomial_weight]
    split_ifs <;> ring
  rw [← he]
  exact quadrature_taylor_closed n hh hf hM

/--
Membership in the specified domain/enclosure: `(∫ t in c-h..c+h,f t)∈output`.

Use: `chebyshev2.Numerics.quadratureJetEnclosure_sound` uses this assertion to establish
membership in the specified domain/enclosure: `(∫ t in c-h..c+h,f t)∈quadratureJetEnclosure
point whole h n`.

Article: chebyshev2, Lemma 20.

Source: chebyshev2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.

Proof: Separate `Even j` from its negation; prove the goal under each of these mutually
exclusive hypotheses. Identify the summands/integrands on their required domain before
replacing the sum or integral.
-/
theorem quadratureCheck_sound_closed {J : IntervalJet} {h R : ℚ} {n : ℕ} {output : IntervalRat}
    (hcheck : quadratureCheck J h R n output=true) {f : ℝ → ℝ} {c : ℝ}
    (hf : ContDiffOn ℝ (n+1) f (Icc (c-h) (c+h)))
    (hpoint : ∀ j<n+1,normalizedWithin f (Icc (c-h) (c+h)) j c∈jetAt J j)
    (hwhole : ∀ t∈Icc (c-h) (c+h),|normalizedWithin f (Icc (c-h) (c+h)) (n+1) t|≤R) :
    (∫ t in c-h..c+h,f t)∈output := by
  -- Separate `Even j` from its negation; prove the goal under each of these mutually exclusive
  -- hypotheses.
  have hp : (0≤h ∧ 0≤R) ∧ intervalSubsetCheck (quadratureEnclosure J h R n) output=true := by
    simpa only [quadratureCheck,Bool.and_eq_true,decide_eq_true_eq] using hcheck
  have hh : 0≤(h:ℝ) := by exact_mod_cast hp.1.1
  have he := quadrature_taylor_even_closed n hh hf hwhole
  let P := ∑ j∈Finset.range (n+1) with Even j,2*(h:ℝ)^(j+1)/(j+1)*normalizedWithin f (Icc (c-h) (c+h)) j c
  have hP : P∈quadraturePolynomial J h n := by
    rw [show P=∑ j∈Finset.range (n+1),
      (quadratureWeight h j:ℝ)*normalizedWithin f (Icc (c-h) (c+h)) j c by
      dsimp [P]
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj : Even j <;> simp [quadratureWeight,hj]]
    apply mem_sumIntervals
    intro j hj
    exact mem_roundHigh (IntervalRat.mem_mul (IntervalRat.mem_singleton _) (hpoint j hj))
  have hrad : (2:ℝ)*R*(h:ℝ)^(n+2)/(n+2)≤quadratureRadius h R n := by
    have hr : 2*R*h^(n+2)/(n+2)≤quadratureRadius h R n := le_max_right _ _
    exact_mod_cast hr
  have herr : |(∫ t in c-h..c+h,f t)-P|≤quadratureRadius h R n := he.trans hrad
  have hmem : (∫ t in c-h..c+h,f t)-P∈(⟨-quadratureRadius h R n,quadratureRadius h R n,
      neg_le_self (le_max_left _ _)⟩:IntervalRat) := by
    simpa only [IntervalRat.mem_def,Rat.cast_neg] using abs_le.mp herr
  apply intervalSubsetCheck_sound hp.2
  simpa only [quadratureEnclosure,add_sub_cancel] using IntervalRat.mem_add hP hmem


end
end chebyshev2.Numerics
