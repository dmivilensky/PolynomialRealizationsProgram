import «2610.05164v2».Numerics.ResidualFlow

/-!
Article: 2610.05164v2, Proposition 13.
Signed dissipative comparison with a varying, nonnegative error budget.
Use: `«2610.05164v2».Numerics.dissipative_abs_barrier` feeds
`«2610.05164v2».Primal.linear_defect_comparison` (linear defect comparison).
Proof chain: `«2610.05164v2».Primal.familyConstraintMap_c1` — 2610.05164v2, Theorem 5.2; Contraction
implies exact feasible density, uniqueness, iteration error and energy bound.
-/
namespace «2610.05164v2».Numerics
noncomputable section
open Set Real
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/--
The stated quantitative bound `e t≤g t`.

Use: `«2610.05164v2».Numerics.dissipative_abs_barrier` uses this bound to establish the stated
quantitative bound `|e t|≤g t`.

Article: 2610.05164v2, Theorem 5.2 via `«2610.05164v2».Primal.familyConstraintMap_c1`.

Proof: Expand/rewrite the named definitions and identities appearing in the tactic block; the
remaining goal is a direct simplification or algebraic consequence.
-/
theorem dissipative_upper_barrier {e c d g g' : ℝ → ℝ} {a b : ℝ}
    (he : ContinuousOn e (Icc a b)) (hg : ContinuousOn g (Icc a b))
    (hed : ∀ t∈Ico a b,HasDerivWithinAt e (c t*e t+d t) (Ici t) t)
    (hgd : ∀ t∈Ico a b,HasDerivWithinAt g (g' t) (Ici t) t)
    (hc : ∀ t∈Ico a b,c t≤0) (hgn : ∀ t∈Ico a b,0≤g t)
    (hd : ∀ t∈Ico a b,d t≤g' t) (h0 : e a≤g a)
    {t : ℝ} (ht : t∈Icc a b) : e t≤g t := by
  -- Expand/rewrite the named definitions and identities appearing in the tactic block; the
  -- remaining goal is a direct simplification or algebraic consequence.
  have H : ∀ ε∈Ioi (0:ℝ),e t≤g t+ε*(t-a) := by
    intro ε hε
    change 0<ε at hε
    apply image_le_of_deriv_right_lt_deriv_boundary' he hed
      (B:=fun x => g x+ε*(x-a)) (B':=fun x => g' x+ε)
    · simpa using h0
    · exact hg.add (continuous_const.mul (continuous_id.sub continuous_const)).continuousOn
    · intro x hx
      convert! (hgd x hx).add
        ((((hasDerivAt_id x).sub_const a).const_mul ε).hasDerivWithinAt) using 1
      simp
    · intro x hx hb
      have hn : 0≤e x := by
        rw [hb]
        exact add_nonneg (hgn x hx) (mul_nonneg hε.le (sub_nonneg.mpr hx.1))
      have hm := mul_nonpos_of_nonpos_of_nonneg (hc x hx) hn
      linarith [hd x hx]
    · exact ht
  -- Establish continuity hlim before using the function at limits or in calculus arguments.
  have hlim : ContinuousWithinAt (fun ε:ℝ => g t+ε*(t-a)) (Ioi 0) 0 := by fun_prop
  have h := continuousWithinAt_const.closure_le
    (show (0:ℝ)∈closure (Ioi 0) by simp) hlim H
  simpa using h

/--
The stated quantitative bound `|e t|≤g t`.

Use: `«2610.05164v2».Primal.linear_defect_comparison` uses this bound to establish the stated
quantitative bound `|y t-z t|≤(K-1)*z t`.

Article: 2610.05164v2, Theorem 5.2 via `«2610.05164v2».Primal.familyConstraintMap_c1`.

Proof: Use the identities/estimates `«2610.05164v2».Numerics.dissipative_upper_barrier` with
the arguments shown in the proof.
-/
theorem dissipative_abs_barrier {e c d g g' : ℝ → ℝ} {a b : ℝ}
    (he : ContinuousOn e (Icc a b)) (hg : ContinuousOn g (Icc a b))
    (hed : ∀ t∈Ico a b,HasDerivWithinAt e (c t*e t+d t) (Ici t) t)
    (hgd : ∀ t∈Ico a b,HasDerivWithinAt g (g' t) (Ici t) t)
    (hc : ∀ t∈Ico a b,c t≤0) (hgn : ∀ t∈Ico a b,0≤g t)
    (hd : ∀ t∈Ico a b,|d t|≤g' t) (h0 : |e a|≤g a)
    {t : ℝ} (ht : t∈Icc a b) : |e t|≤g t := by
  -- Use the identities/estimates `«2610.05164v2».Numerics.dissipative_upper_barrier` with the
  -- arguments shown in the proof.
  have hu := dissipative_upper_barrier he hg hed hgd hc hgn
    (fun x hx => (le_abs_self _).trans (hd x hx)) ((le_abs_self _).trans h0) ht
  have hl := dissipative_upper_barrier (e:=fun x => -e x) (c:=c) (d:=fun x => -d x) he.neg hg
    (fun x hx => by convert! (hed x hx).neg using 1;ring) hgd hc hgn
    (fun x hx => (neg_le_abs _).trans (hd x hx)) ((neg_le_abs _).trans h0) ht
  change -e t≤g t at hl
  exact abs_le.mpr ⟨by linarith,hu⟩

end
end «2610.05164v2».Numerics
