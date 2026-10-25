import chebyshev2.Numerics.ForwardTaylor

/-!
Article: chebyshev2, Lemma 24.
Upper-bound rules used by Lemma 24.
Use: `chebyshev2.Numerics.concave_quadratic_upper` feeds
`chebyshev2.Numerics.StateJetOn.state_concavity_upper` (state concavity upper).
Proof chain: `chebyshev2.Numerics.StateJetOn.state_concavity_upper` — chebyshev2, Lemma 24;
Actual multivariable segment, state and time Taylor/concavity upper bounds.
-/
namespace chebyshev2.Numerics
noncomputable section
open Set Real
set_option autoImplicit false
set_option maxHeartbeats 1000000

/--
The stated quantitative bound `f x≤f u`.

Use: a standalone supporting bound for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Lemma 24.

Proof: Expand/rewrite the named definitions and identities appearing in the tactic block; the
remaining goal is a direct simplification or algebraic consequence.
-/
theorem monotone_face_upper {f : ℝ → ℝ} {l u x : ℝ}
    (hf : ContinuousOn f (Icc l u)) (hd : DifferentiableOn ℝ f (Ioo l u))
    (hpos : ∀ t∈Ioo l u,0≤deriv f t) (hx : x∈Icc l u) : f x≤f u := by
  have hm := monotoneOn_of_deriv_nonneg (convex_Icc l u) hf
    (by simpa only [interior_Icc] using hd) (by simpa only [interior_Icc] using hpos)
  exact hm hx ⟨hx.1.trans hx.2,le_rfl⟩ hx.2

/--
The stated quantitative bound `f x≤f l`.

Use: a standalone supporting bound for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Lemma 24.

Proof: Expand/rewrite the named definitions and identities appearing in the tactic block; the
remaining goal is a direct simplification or algebraic consequence.
-/
theorem antitone_face_upper {f : ℝ → ℝ} {l u x : ℝ}
    (hf : ContinuousOn f (Icc l u)) (hd : DifferentiableOn ℝ f (Ioo l u))
    (hneg : ∀ t∈Ioo l u,deriv f t≤0) (hx : x∈Icc l u) : f x≤f l := by
  have hm := antitoneOn_of_deriv_nonpos (convex_Icc l u) hf
    (by simpa only [interior_Icc] using hd) (by simpa only [interior_Icc] using hneg)
  exact hm ⟨le_rfl,hx.1.trans hx.2⟩ hx hx.1

/--
The stated quantitative bound `f 1≤β+g+H/2`.

Use: `chebyshev2.Numerics.hessian_segment_upper` uses this bound to establish the stated
quantitative bound `f 1≤β+(αT*gU^2+αU*gT^2+2*γ*gU*gT)/(2*(αU*αT-γ^2))`.

Article: chebyshev2, Lemma 24 via `chebyshev2.Numerics.StateJetOn.segment_taylor_upper`.

Proof: Use the identities/estimates `chebyshev2.Numerics.forward_taylor_remainder`,
`chebyshev2.Numerics.normalizedWithin_zero` with the arguments shown in the proof.
-/
theorem second_order_segment_upper {f : ℝ → ℝ} {β g H : ℝ}
    (hf : ContDiffOn ℝ 2 f (Icc (0:ℝ) 1)) (h0 : f 0≤β)
    (hg : normalizedWithin f (Icc (0:ℝ) 1) 1 0=g)
    (hH : ∀ t∈Icc (0:ℝ) 1,2*normalizedWithin f (Icc (0:ℝ) 1) 2 t≤H) :
    f 1≤β+g+H/2 := by
  -- Use the identities/estimates `chebyshev2.Numerics.forward_taylor_remainder`,
  -- `chebyshev2.Numerics.normalizedWithin_zero` with the arguments shown in the proof.
  obtain ⟨ξ,hξ,he⟩ := forward_taylor_remainder (f := f) (a := 0) (h := 1)
    (v := 1) 1 (by norm_num) (by norm_num) (by convert hf using 1 <;> norm_num)
  have hHξ := hH ξ ⟨hξ.1.le,hξ.2.le⟩
  simp only [zero_add,Finset.sum_range_succ,Finset.sum_range_zero,
    normalizedWithin_zero,one_pow,mul_one,hg] at he
  linarith

/--
The unrestricted maximum of the concave two-variable quadratic in Lemma 24(iv), proved by an
explicit sum-of-squares identity.

The stated quantitative bound `gU*u+gT*v-(αU*u^2-2*γ*u*v+αT*v^2)/2≤
(αT*gU^2+αU*gT^2+2*γ*gU*gT)/(2*(αU*αT-γ^2))`.

Use: `chebyshev2.Numerics.hessian_segment_upper` uses this bound to establish the stated
quantitative bound `f 1≤β+(αT*gU^2+αU*gT^2+2*γ*gU*gT)/(2*(αU*αT-γ^2))`.

Article: chebyshev2, Lemma 24 via `chebyshev2.Numerics.StateJetOn.state_concavity_upper`.

Proof: Expand/rewrite the named definitions and identities appearing in the tactic block; the
remaining goal is a direct simplification or algebraic consequence.
-/
theorem concave_quadratic_upper {αU αT γ gU gT u v : ℝ}
    (ha : 0<αU) (hD : 0<αU*αT-γ^2) :
    gU*u+gT*v-(αU*u^2-2*γ*u*v+αT*v^2)/2≤
      (αT*gU^2+αU*gT^2+2*γ*gU*gT)/(2*(αU*αT-γ^2)) := by
  -- Expand/rewrite the named definitions and identities appearing in the tactic block; the
  -- remaining goal is a direct simplification or algebraic consequence.
  let D := αU*αT-γ^2
  let Q := gU*u+gT*v-(αU*u^2-2*γ*u*v+αT*v^2)/2
  let P := αT*gU^2+αU*gT^2+2*γ*gU*gT
  have he : αU*(P-2*D*Q)=
      (D*v-(αU*gT+γ*gU))^2+D*(αU*u-γ*v-gU)^2 := by dsimp [P,D,Q];ring
  have hnn : 0≤P-2*D*Q := by
    apply (mul_nonneg_iff_of_pos_left ha).mp
    rw [he]
    exact add_nonneg (sq_nonneg _) (mul_nonneg hD.le (sq_nonneg _))
  apply (le_div_iff₀ (show 0<2*D by positivity)).mpr
  change Q*(2*D)≤P
  linarith

/--
The stated quantitative bound `g*v-α*v^2/2≤g^2/(2*α)`.

Use: `chebyshev2.Numerics.StateJetOn.state_concavity_upper_fixed_T` uses this bound to
establish the stated quantitative bound `F.value (c+v)≤β+g^2/(2*α)`.

Article: chebyshev2, Lemma 24.

Proof: The tactic block explicitly constructs the required witness or reduces the goal to the
local facts stated below.
-/
theorem concave_quadratic_upper_one {α g v : ℝ} (hα : 0<α) :
    g*v-α*v^2/2≤g^2/(2*α) := by
  apply (le_div_iff₀ (by positivity : 0<2*α)).mpr
  nlinarith [sq_nonneg (α*v-g)]

/--
Combining the actual Taylor bound with the maximum formula. The supplied curvature bound is on
the actual second derivative along the state segment.

The stated quantitative bound `f 1≤β+(αT*gU^2+αU*gT^2+2*γ*gU*gT)/(2*(αU*αT-γ^2))`.

Use: a standalone supporting bound for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Lemma 24.

Proof: Use the identities/estimates `chebyshev2.Numerics.second_order_segment_upper`,
`chebyshev2.Numerics.concave_quadratic_upper` with the arguments shown in the proof.
-/
theorem hessian_segment_upper {f : ℝ → ℝ} {β αU αT γ gU gT u v : ℝ}
    (hf : ContDiffOn ℝ 2 f (Icc (0:ℝ) 1)) (h0 : f 0≤β)
    (hg : normalizedWithin f (Icc (0:ℝ) 1) 1 0≤gU*u+gT*v)
    (hH : ∀ t∈Icc (0:ℝ) 1,
      2*normalizedWithin f (Icc (0:ℝ) 1) 2 t≤-(αU*u^2-2*γ*u*v+αT*v^2))
    (ha : 0<αU) (hD : 0<αU*αT-γ^2) :
    f 1≤β+(αT*gU^2+αU*gT^2+2*γ*gU*gT)/(2*(αU*αT-γ^2)) := by
  -- Use the identities/estimates `chebyshev2.Numerics.second_order_segment_upper`,
  -- `chebyshev2.Numerics.concave_quadratic_upper` with the arguments shown in the proof.
  have ht := second_order_segment_upper hf h0 rfl hH
  have hm := concave_quadratic_upper (u := u) (v := v) (gU := gU) (gT := gT) ha hD
  linarith

end
end chebyshev2.Numerics
