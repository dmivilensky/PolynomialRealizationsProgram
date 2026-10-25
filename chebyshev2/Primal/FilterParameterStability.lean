import chebyshev2.Primal.Filters
import chebyshev2.Primal.ParameterBounds
import chebyshev2.Numerics.ResidualFlow

/-!
Article: chebyshev2, Proposition 13.
Multiplicative comparison for parameter-dependent Riccati filters.
Use: `chebyshev2.Primal.nonlinearFilter_parameter_enclosed` feeds
`chebyshev2.Primal.familyNonlinearFilter_parameter_bound` (family Nonlinear Filter parameter
bound).
Proof chain: `chebyshev2.Primal.familyConstraintMap_c1` — chebyshev2, Theorem 5.2; Contraction
implies exact feasible density, uniqueness, iteration error and energy bound.
-/
namespace chebyshev2.Primal
noncomputable section
open Set Real
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/--
The stated quantitative bound `y t≤K*z t`.

Use: `chebyshev2.Primal.nonlinearFilter_parameter_upper` uses this bound to establish the
stated quantitative bound `1+nonlinearFilter hφ κ s t≤exp d*(1+nonlinearFilter hψ κ s t)`.

Article: chebyshev2, Theorem 5.2 via `chebyshev2.Primal.familyConstraintMap_c1`.

Proof: Expand/rewrite the named definitions and identities appearing in the tactic block; the
remaining goal is a direct simplification or algebraic consequence.
-/
theorem scaled_riccati_comparison {y z A c P Q : ℝ → ℝ} {a b K : ℝ}
    (hy : ContinuousOn y (Icc a b)) (hz : ContinuousOn z (Icc a b))
    (hyd : ∀ t∈Ico a b,HasDerivWithinAt y (A t+c t*P t-P t*(y t)^2) (Ici t) t)
    (hzd : ∀ t∈Ico a b,HasDerivWithinAt z (A t+c t*Q t-Q t*(z t)^2) (Ici t) t)
    (hK : 1≤K) (hA : ∀ t∈Ico a b,0≤A t) (hc : ∀ t∈Ico a b,0≤c t)
    (hP : ∀ t∈Ico a b,0≤P t)
    (hPQ : ∀ t∈Ico a b,P t≤K*Q t) (hQP : ∀ t∈Ico a b,Q t≤K*P t)
    (hz0 : ∀ t∈Ico a b,0≤z t) (h0 : y a≤K*z a)
    {t : ℝ} (ht : t∈Icc a b) : y t≤K*z t := by
  -- Expand/rewrite the named definitions and identities appearing in the tactic block; the
  -- remaining goal is a direct simplification or algebraic consequence.
  have hK0 : 0≤K := zero_le_one.trans hK
  have H : ∀ ε∈Ioi (0:ℝ),y t≤K*z t+ε*(t-a) := by
    intro ε hε
    change 0<ε at hε
    apply image_le_of_deriv_right_lt_deriv_boundary' hy hyd
      (B:=fun x => K*z x+ε*(x-a))
      (B':=fun x => K*(A x+c x*Q x-Q x*(z x)^2)+ε)
    · simpa using h0
    · exact (hz.const_mul K).add ((continuous_const.mul
        (continuous_id.sub continuous_const)).continuousOn)
    · intro x hx
      convert! ((hzd x hx).const_mul K).add
        ((((hasDerivAt_id x).sub_const a).const_mul ε).hasDerivWithinAt) using 1
      simp
    · intro x hx hboundary
      have hb : K*z x≤y x := by
        rw [hboundary]
        exact le_add_of_nonneg_right (mul_nonneg hε.le (sub_nonneg.mpr hx.1))
      have hs : (K*z x)^2≤(y x)^2 :=
        pow_le_pow_left₀ (mul_nonneg hK0 (hz0 x hx)) hb 2
      have h1 := mul_nonpos_of_nonneg_of_nonpos (hA x hx) (sub_nonpos.mpr hK)
      have h2 := mul_nonpos_of_nonneg_of_nonpos (hc x hx) (sub_nonpos.mpr (hPQ x hx))
      have h3 := mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos hK0 (sub_nonpos.mpr (hQP x hx))) (sq_nonneg (z x))
      have h4 := mul_nonpos_of_nonneg_of_nonpos (hP x hx) (sub_nonpos.mpr hs)
      have hid : A x+c x*P x-P x*(y x)^2-
          K*(A x+c x*Q x-Q x*(z x)^2)=
          A x*(1-K)+c x*(P x-K*Q x)+K*(Q x-K*P x)*(z x)^2+
            P x*((K*z x)^2-(y x)^2) := by ring
      have hdiff : A x+c x*P x-P x*(y x)^2-
          K*(A x+c x*Q x-Q x*(z x)^2)≤0 := by
        rw [hid]
        exact add_nonpos (add_nonpos (add_nonpos h1 h2) h3) h4
      exact (sub_nonpos.mp hdiff).trans_lt (lt_add_of_pos_right _ hε)
    · exact ht
  -- Establish continuity hlim before using the function at limits or in calculus arguments.
  have hlim : ContinuousWithinAt (fun ε:ℝ => K*z t+ε*(t-a)) (Ioi 0) 0 := by fun_prop
  have hh := continuousWithinAt_const.closure_le
    (show (0:ℝ)∈closure (Ioi 0) by simp) hlim H
  simpa using hh

/--
The stated quantitative bound `normalizedVelocity φ t≤exp d*normalizedVelocity ψ t`.

Use: `chebyshev2.Primal.nonlinearFilter_parameter_upper` uses this bound to establish the
stated quantitative bound `1+nonlinearFilter hφ κ s t≤exp d*(1+nonlinearFilter hψ κ s t)`.

Article: chebyshev2, Theorem 5.2 via `chebyshev2.Primal.familyConstraintMap_c1`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem normalizedVelocity_comparison {φ ψ : ℝ → ℝ} {d t : ℝ}
    (h : |φ t-ψ t|≤d) : normalizedVelocity φ t≤exp d*normalizedVelocity ψ t := by
  have hl := (abs_le.mp h).1
  calc
    normalizedVelocity φ t=3*exp (-φ t) := rfl
    _≤3*exp (d-ψ t) := mul_le_mul_of_nonneg_left (exp_le_exp.mpr (by linarith)) (by norm_num)
    _=exp d*normalizedVelocity ψ t := by rw [sub_eq_add_neg,exp_add];unfold normalizedVelocity;ring

/--
The derivative within the stated domain: `HasDerivWithinAt (fun t => 1+nonlinearFilter hφ κ s
t) (3*(s/κ)*t^2+(1+(s/κ)*t^3*(2-t^3))*normalizedVelocity φ t- normalizedVelocity φ
t*(1+nonlinearFilter hφ κ s t)^2) (Icc (0:ℝ) 1) t`.

Use: `chebyshev2.Primal.nonlinearFilter_parameter_upper` uses this derivative formula to
establish the stated quantitative bound `1+nonlinearFilter hφ κ s t≤exp d*(1+nonlinearFilter hψ
κ s t)`.

Article: chebyshev2, Theorem 5.2 via `chebyshev2.Primal.familyConstraintMap_c1`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem shifted_nonlinear_ode {φ : ℝ → ℝ} (hφ : Continuous φ)
    {κ s t : ℝ} (hκ : 0<κ) (hs : 0≤s) (ht : t∈Icc (0:ℝ) 1) :
    HasDerivWithinAt (fun t => 1+nonlinearFilter hφ κ s t)
      (3*(s/κ)*t^2+(1+(s/κ)*t^3*(2-t^3))*normalizedVelocity φ t-
        normalizedVelocity φ t*(1+nonlinearFilter hφ κ s t)^2) (Icc (0:ℝ) 1) t := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  convert! (nonlinearFilter_ode hφ hκ hs ht).const_add 1 using 1
  unfold normalizedVelocity normalizedDensity
  rw [exp_neg]
  field_simp [hκ.ne',exp_ne_zero]
  ring

/--
Uniform multiplicative control on the complete left half, including the join. No parameter
differentiability or numerical solution tube is assumed.

The stated quantitative bound `1+nonlinearFilter hφ κ s t≤exp d*(1+nonlinearFilter hψ κ s t)`.

Use: `chebyshev2.Primal.nonlinearFilter_parameter_enclosed` uses this bound to establish
the stated quantitative bound `exp (-d)*(1+nonlinearFilter hψ κ s t)≤1+nonlinearFilter hφ κ s t
∧ 1+nonlinearFilter hφ κ s t≤exp d*(1+nonlinearFilter hψ κ s t)`.

Article: chebyshev2, Theorem 5.2 via `chebyshev2.Primal.familyConstraintMap_c1`.

Proof: Use the identities/estimates `chebyshev2.Primal.scaled_riccati_comparison`,
`chebyshev2.Primal.nonlinearFilter_continuous`,
`chebyshev2.Primal.shifted_nonlinear_ode` with the arguments shown in the proof.
-/
theorem nonlinearFilter_parameter_upper {φ ψ : ℝ → ℝ}
    (hφ : Continuous φ) (hψ : Continuous ψ) {κ s d : ℝ}
    (hκ : 0<κ) (hs : 0≤s) (hd : 0≤d)
    (hprofile : ∀ t∈Icc (0:ℝ) 1,|φ t-ψ t|≤d)
    {t : ℝ} (ht : t∈Icc (0:ℝ) 1) :
    1+nonlinearFilter hφ κ s t≤exp d*(1+nonlinearFilter hψ κ s t) := by
  -- Use the identities/estimates `chebyshev2.Primal.scaled_riccati_comparison`,
  -- `chebyshev2.Primal.nonlinearFilter_continuous`,
  -- `chebyshev2.Primal.shifted_nonlinear_ode` with the arguments shown in the proof.
  let A := fun t:ℝ => 3*(s/κ)*t^2
  let c := fun t:ℝ => 1+(s/κ)*t^3*(2-t^3)
  apply scaled_riccati_comparison
    ((nonlinearFilter_continuous hφ hκ hs).const_add 1).continuousOn
    ((nonlinearFilter_continuous hψ hκ hs).const_add 1).continuousOn
    (A:=A) (c:=c) (P:=normalizedVelocity φ) (Q:=normalizedVelocity ψ)
  · intro x hx
    exact (shifted_nonlinear_ode hφ hκ hs ⟨hx.1,hx.2.le⟩).mono_of_mem_nhdsWithin
      (Filter.mem_of_superset (Icc_mem_nhdsGE hx.2) (fun z hz => ⟨hx.1.trans hz.1,hz.2⟩))
  · intro x hx
    exact (shifted_nonlinear_ode hψ hκ hs ⟨hx.1,hx.2.le⟩).mono_of_mem_nhdsWithin
      (Filter.mem_of_superset (Icc_mem_nhdsGE hx.2) (fun z hz => ⟨hx.1.trans hz.1,hz.2⟩))
  · exact one_le_exp_iff.mpr hd
  · intro x _
    dsimp [A]
    positivity
  · intro x hx
    have hx3 : x^3≤1 := pow_le_one₀ hx.1 hx.2.le
    have h2 : 0≤2-x^3 := by linarith
    dsimp [c]
    exact add_nonneg zero_le_one (mul_nonneg
      (mul_nonneg (div_nonneg hs hκ.le) (pow_nonneg hx.1 _)) h2)
  · intro x _
    unfold normalizedVelocity
    positivity
  · intro x hx
    exact normalizedVelocity_comparison (hprofile x ⟨hx.1,hx.2.le⟩)
  · intro x hx
    apply normalizedVelocity_comparison
    simpa only [abs_sub_comm] using hprofile x ⟨hx.1,hx.2.le⟩
  · intro x _
    exact add_nonneg (by norm_num) (nonlinearFilter_nonneg hψ hκ hs x)
  · rw [nonlinearFilter_initial,nonlinearFilter_initial]
    simpa using one_le_exp_iff.mpr hd
  · exact ht

/--
The stated quantitative bound `exp (-d)*(1+nonlinearFilter hψ κ s t)≤1+nonlinearFilter hφ κ s t
∧ 1+nonlinearFilter hφ κ s t≤exp d*(1+nonlinearFilter hψ κ s t)`.

Use: `chebyshev2.Primal.familyNonlinearFilter_parameter_bound` uses this bound to establish
the stated quantitative bound `|familyNonlinearFilter hψ hθ κ s reflected a
t-familyNonlinearFilter hψ hθ κ s reflected b t|≤ (exp (‖a-b‖*∑ i,‖unitDirection (hθ
i)‖)-1)*(1+2*s/κ)`.

Article: chebyshev2, Theorem 5.2 via `chebyshev2.Primal.familyConstraintMap_c1`.

Proof: Use the identities/estimates `chebyshev2.Primal.nonlinearFilter_parameter_upper`
with the arguments shown in the proof.
-/
theorem nonlinearFilter_parameter_enclosed {φ ψ : ℝ → ℝ}
    (hφ : Continuous φ) (hψ : Continuous ψ) {κ s d : ℝ}
    (hκ : 0<κ) (hs : 0≤s) (hd : 0≤d)
    (hprofile : ∀ t∈Icc (0:ℝ) 1,|φ t-ψ t|≤d)
    {t : ℝ} (ht : t∈Icc (0:ℝ) 1) :
    exp (-d)*(1+nonlinearFilter hψ κ s t)≤1+nonlinearFilter hφ κ s t ∧
    1+nonlinearFilter hφ κ s t≤exp d*(1+nonlinearFilter hψ κ s t) := by
  -- Use the identities/estimates `chebyshev2.Primal.nonlinearFilter_parameter_upper` with
  -- the arguments shown in the proof.
  refine ⟨?_,nonlinearFilter_parameter_upper hφ hψ hκ hs hd hprofile ht⟩
  have h := nonlinearFilter_parameter_upper hψ hφ hκ hs hd
    (fun x hx => by simpa only [abs_sub_comm] using hprofile x hx) ht
  rw [exp_neg]
  exact (inv_mul_le_iff₀ (exp_pos d)).mpr h

end
end chebyshev2.Primal
