import chebyshev2.Primal.FilterBounds
import chebyshev2.Numerics.DissipativeBarrier

/-!
Article: chebyshev2, Proposition 13.
A lower ground-coordinate bound for the linear primal filter.
Use: `chebyshev2.Primal.reflectedLinearFilter_lower` feeds
`chebyshev2.Primal.reflectedLinearFilter_parameter_bound` (reflected Linear Filter parameter
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
The derivative within the stated domain: `HasDerivWithinAt (linearFilter hφ κ)
(3*t^2+normalizedVelocity φ t*(t^3*(2-t^3)-2*linearFilter hφ κ t)) (Icc (0:ℝ) 1) t`.

Use: `chebyshev2.Primal.linearFilter_lower` uses this derivative formula to establish the
stated quantitative bound `t^3*(2-t^3)/2≤linearFilter hφ κ t`.

Article: chebyshev2, Theorem 5.2 via `chebyshev2.Primal.familyConstraintMap_c1`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem linearFilter_regular_ode {φ : ℝ → ℝ} (hφ : Continuous φ) {κ t : ℝ}
    (hκ : 0<κ) (ht : t∈Icc (0:ℝ) 1) :
    HasDerivWithinAt (linearFilter hφ κ)
      (3*t^2+normalizedVelocity φ t*(t^3*(2-t^3)-2*linearFilter hφ κ t)) (Icc (0:ℝ) 1) t := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  convert! linearFilter_ode hφ hκ ht using 1
  unfold normalizedVelocity normalizedDensity
  rw [exp_neg]
  field_simp [hκ.ne',exp_ne_zero]
  ring

/--
The stated quantitative bound `t^3*(2-t^3)/2≤linearFilter hφ κ t`.

Use: `chebyshev2.Primal.reflectedLinearFilter_lower` uses this bound to establish the
stated quantitative bound `t^3*(2-t^3)/2≤reflectedLinearFilter hφ κ t`.

Article: chebyshev2, Theorem 5.2 via `chebyshev2.Primal.familyConstraintMap_c1`.

Proof: Use the identities/estimates `chebyshev2.Primal.linearFilter_continuous`,
`chebyshev2.Primal.linearFilter_regular_ode`,
`chebyshev2.Numerics.dissipative_upper_barrier` with the arguments shown in the proof.
-/
theorem linearFilter_lower {φ : ℝ → ℝ} (hφ : Continuous φ) {κ t : ℝ}
    (hκ : 0<κ) (ht : t∈Icc (0:ℝ) 1) : t^3*(2-t^3)/2≤linearFilter hφ κ t := by
  -- Use the identities/estimates `chebyshev2.Primal.linearFilter_continuous`,
  -- `chebyshev2.Primal.linearFilter_regular_ode`,
  -- `chebyshev2.Numerics.dissipative_upper_barrier` with the arguments shown in the proof.
  let e := fun t:ℝ => t^3*(2-t^3)/2-linearFilter hφ κ t
  -- Establish continuity he before using the function at limits or in calculus arguments.
  have he : Continuous e := by
    have h := linearFilter_continuous hφ hκ
    dsimp [e]
    fun_prop
  have hed (x : ℝ) (hx : x∈Ico (0:ℝ) 1) :
      HasDerivWithinAt e (-2*normalizedVelocity φ x*e x-3*x^5) (Ici x) x := by
    have hp := (((hasDerivAt_id x).pow 3).mul (((hasDerivAt_id x).pow 3).const_sub 2)).div_const 2
    have hr := (linearFilter_regular_ode hφ hκ ⟨hx.1,hx.2.le⟩).mono_of_mem_nhdsWithin
      (Filter.mem_of_superset (Icc_mem_nhdsGE hx.2) (fun z hz => ⟨hx.1.trans hz.1,hz.2⟩))
    convert! hp.hasDerivWithinAt.sub hr using 1
    dsimp only [e]
    simp only [Pi.pow_apply,id_eq]
    ring
  have h := chebyshev2.Numerics.dissipative_upper_barrier he.continuousOn continuous_const.continuousOn
    hed (g:=fun _ => (0:ℝ)) (g':=fun _ => (0:ℝ))
    (fun x _ => (hasDerivWithinAt_const x _ (0:ℝ)))
    (fun x _ => mul_nonpos_of_nonpos_of_nonneg (by norm_num) (by unfold normalizedVelocity;positivity))
    (fun _ _ => le_rfl) (fun x hx => by exact neg_nonpos.mpr (mul_nonneg (by norm_num) (pow_nonneg hx.1 _)))
    (by simp [e,linearFilter_initial]) ht
  exact sub_nonpos.mp h

/--
Defines `rightLinearFilter` of type `ℝ` by `reflectedLinearFilter hφ κ (2-v)`.

Use: `chebyshev2.Primal.reflectedLinearFilter_lower` uses this definition to establish the
stated quantitative bound `t^3*(2-t^3)/2≤reflectedLinearFilter hφ κ t`.

Article: chebyshev2, Theorem 5.2 via `chebyshev2.Primal.familyConstraintMap_c1`.
-/
def rightLinearFilter {φ : ℝ → ℝ} (hφ : Continuous φ) (κ v : ℝ) : ℝ :=
  reflectedLinearFilter hφ κ (2-v)

/--
The derivative within the stated domain: `HasDerivWithinAt (rightLinearFilter hφ κ)
(3*(2-v)^2+normalizedVelocity φ (2-v)* ((2-v)^3*(2-(2-v)^3)-2*rightLinearFilter hφ κ v)) (Icc
(1:ℝ) 2) v`.

Use: `chebyshev2.Primal.reflectedLinearFilter_lower` uses this derivative formula to
establish the stated quantitative bound `t^3*(2-t^3)/2≤reflectedLinearFilter hφ κ t`.

Article: chebyshev2, Theorem 5.2 via `chebyshev2.Primal.familyConstraintMap_c1`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem rightLinearFilter_regular_ode {φ : ℝ → ℝ} (hφ : Continuous φ) {κ v : ℝ}
    (hκ : 0<κ) (hv : v∈Icc (1:ℝ) 2) :
    HasDerivWithinAt (rightLinearFilter hφ κ)
      (3*(2-v)^2+normalizedVelocity φ (2-v)*
        ((2-v)^3*(2-(2-v)^3)-2*rightLinearFilter hφ κ v)) (Icc (1:ℝ) 2) v := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  have ht : 2-v∈Icc (0:ℝ) 1 := by constructor <;> linarith [hv.1,hv.2]
  have h := (reflectedLinearFilter_ode hφ hκ ht).comp v
    ((hasDerivWithinAt_id v (Icc (1:ℝ) 2)).const_sub 2) (by
      intro x hx
      constructor <;> linarith [hx.1,hx.2])
  convert! h using 1
  dsimp only [rightLinearFilter,normalizedVelocity,normalizedDensity]
  rw [exp_neg]
  field_simp [hκ.ne',exp_ne_zero]
  ring

/--
The stated quantitative bound `t^3*(2-t^3)/2≤reflectedLinearFilter hφ κ t`.

Use: `chebyshev2.Primal.reflectedLinearFilter_parameter_bound` uses this bound to establish
the stated quantitative bound `|reflectedLinearFilter hφ κ t-reflectedLinearFilter hψ κ t|≤
(exp d-1)*(2-t^3-reflectedLinearFilter hψ κ t)`.

Article: chebyshev2, Theorem 5.2 via `chebyshev2.Primal.familyConstraintMap_c1`.

Proof: Use the identities/estimates `chebyshev2.Primal.reflectedLinearFilter_continuous`,
`chebyshev2.Primal.rightLinearFilter_regular_ode`,
`chebyshev2.Primal.linearFilter_lower` with the arguments shown in the proof.
-/
theorem reflectedLinearFilter_lower {φ : ℝ → ℝ} (hφ : Continuous φ) {κ t : ℝ}
    (hκ : 0<κ) (ht : t∈Icc (0:ℝ) 1) : t^3*(2-t^3)/2≤reflectedLinearFilter hφ κ t := by
  -- Use the identities/estimates `chebyshev2.Primal.reflectedLinearFilter_continuous`,
  -- `chebyshev2.Primal.rightLinearFilter_regular_ode`,
  -- `chebyshev2.Primal.linearFilter_lower` with the arguments shown in the proof.
  let q := fun v:ℝ => 2-(2-v)^3
  let e := fun v:ℝ => q v*(2-q v)/2-rightLinearFilter hφ κ v
  -- Establish continuity he before using the function at limits or in calculus arguments.
  have he : Continuous e := by
    -- Establish continuity h before using the function at limits or in calculus arguments.
    have h : Continuous (rightLinearFilter hφ κ) :=
      (reflectedLinearFilter_continuous hφ hκ).comp (continuous_const.sub continuous_id)
    dsimp [e,q]
    fun_prop
  have hed (x : ℝ) (hx : x∈Ico (1:ℝ) 2) :
      HasDerivWithinAt e (-2*normalizedVelocity φ (2-x)*e x-3*q x*(2-x)^2) (Ici x) x := by
    have hq := (((hasDerivAt_id x).const_sub 2).pow 3).const_sub 2
    have hp := (hq.mul (hq.const_sub 2)).div_const 2
    have hr := (rightLinearFilter_regular_ode hφ hκ ⟨hx.1,hx.2.le⟩).mono_of_mem_nhdsWithin
      (Filter.mem_of_superset (Icc_mem_nhdsGE hx.2) (fun z hz => ⟨hx.1.trans hz.1,hz.2⟩))
    convert! hp.hasDerivWithinAt.sub hr using 1
    dsimp only [e,q]
    simp only [Pi.pow_apply,id_eq]
    ring
  have h0 : e 1≤0 := by
    have h := linearFilter_lower hφ hκ (t:=1) (by norm_num)
    rw [linearFilter_join] at h
    norm_num [e,q,rightLinearFilter] at h ⊢
    linarith
  have hv : 2-t∈Icc (1:ℝ) 2 := ⟨by linarith [ht.2],by linarith [ht.1]⟩
  have h := chebyshev2.Numerics.dissipative_upper_barrier he.continuousOn continuous_const.continuousOn
    hed (g:=fun _ => (0:ℝ)) (g':=fun _ => (0:ℝ))
    (fun x _ => (hasDerivWithinAt_const x _ (0:ℝ)))
    (fun x _ => mul_nonpos_of_nonpos_of_nonneg (by norm_num) (by unfold normalizedVelocity;positivity))
    (fun _ _ => le_rfl) (fun x hx => by
      have hn : 0≤q x := by
        have hc : (2-x)^3≤1 := pow_le_one₀ (by linarith [hx.2]) (by linarith [hx.1])
        dsimp [q]
        linarith
      exact neg_nonpos.mpr (mul_nonneg (mul_nonneg (by norm_num) hn) (sq_nonneg _))) h0 hv
  dsimp only [e,q,rightLinearFilter] at h
  simp only [sub_sub_cancel] at h
  simpa only [mul_comm] using sub_nonpos.mp h

end
end chebyshev2.Primal
