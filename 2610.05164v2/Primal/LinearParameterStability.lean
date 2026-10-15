import «2610.05164v2».Primal.LinearLowerBound
import «2610.05164v2».Primal.FilterParameterStability

/-!
Article: 2610.05164v2, Proposition 13.
Sharp parameter comparison for the monotone linear-filter defect.
Use: `«2610.05164v2».Primal.reflectedLinearFilter_parameter_bound` feeds
`«2610.05164v2».Primal.familyLinearFilter_parameter_bound` (family Linear Filter parameter bound).
Proof chain: `«2610.05164v2».Primal.familyConstraintMap_c1` — 2610.05164v2, Theorem 5.2; Contraction
implies exact feasible density, uniqueness, iteration error and energy bound.
-/
namespace «2610.05164v2».Primal
noncomputable section
open Set Real
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/--
The stated quantitative bound `|p-q|≤(K-1)*q`.

Use: `«2610.05164v2».Primal.normalizedVelocity_difference` uses this bound to establish the
stated quantitative bound `|normalizedVelocity φ t-normalizedVelocity ψ t|≤(exp
d-1)*normalizedVelocity ψ t`.

Article: 2610.05164v2, Theorem 5.2 via `«2610.05164v2».Primal.familyConstraintMap_c1`.

Proof: Expand/rewrite the named definitions and identities appearing in the tactic block; the
remaining goal is a direct simplification or algebraic consequence.
-/
theorem relative_difference_bound {p q K : ℝ} (hq : 0≤q) (hK : 1≤K)
    (hpq : p≤K*q) (hqp : q≤K*p) : |p-q|≤(K-1)*q := by
  -- Expand/rewrite the named definitions and identities appearing in the tactic block; the
  -- remaining goal is a direct simplification or algebraic consequence.
  have hKp : 0<K := zero_lt_one.trans_le hK
  have hsum : 0≤K*p-q+q*(K-1)^2 :=
    add_nonneg (sub_nonneg.mpr hqp) (mul_nonneg hq (sq_nonneg _))
  have hid : K*p-q+q*(K-1)^2=K*(p-(2-K)*q) := by ring
  rw [hid] at hsum
  have hlo := nonneg_of_mul_nonneg_right hsum hKp
  exact abs_le.mpr ⟨by nlinarith,by nlinarith⟩

/--
The stated quantitative bound `|normalizedVelocity φ t-normalizedVelocity ψ t|≤(exp
d-1)*normalizedVelocity ψ t`.

Use: `«2610.05164v2».Primal.linearFilter_parameter_bound` uses this bound to establish the
stated quantitative bound `|linearFilter hφ κ t-linearFilter hψ κ t|≤(exp d-1)*linearDefect hψ
κ t`.

Article: 2610.05164v2, Theorem 5.2 via `«2610.05164v2».Primal.familyConstraintMap_c1`.

Proof: Use the identities/estimates `«2610.05164v2».Primal.relative_difference_bound`,
`«2610.05164v2».Primal.normalizedVelocity_comparison` with the arguments shown in the proof.
-/
theorem normalizedVelocity_difference {φ ψ : ℝ → ℝ} {d t : ℝ}
    (hd : 0≤d) (h : |φ t-ψ t|≤d) :
    |normalizedVelocity φ t-normalizedVelocity ψ t|≤(exp d-1)*normalizedVelocity ψ t :=
  relative_difference_bound (by unfold normalizedVelocity;positivity)
    (one_le_exp_iff.mpr hd) (normalizedVelocity_comparison h)
    (normalizedVelocity_comparison (by simpa only [abs_sub_comm] using h))

/--
The stated quantitative bound `|y t-z t|≤(K-1)*z t`.

Use: `«2610.05164v2».Primal.linearFilter_parameter_bound` uses this bound to establish the
stated quantitative bound `|linearFilter hφ κ t-linearFilter hψ κ t|≤(exp d-1)*linearDefect hψ
κ t`.

Article: 2610.05164v2, Theorem 5.2 via `«2610.05164v2».Primal.familyConstraintMap_c1`.

Proof: Use the identities/estimates `«2610.05164v2».Numerics.dissipative_abs_barrier` with the
arguments shown in the proof.
-/
theorem linear_defect_comparison {y z P Q q : ℝ → ℝ} {a b K : ℝ}
    (hy : ContinuousOn y (Icc a b)) (hz : ContinuousOn z (Icc a b))
    (hyd : ∀ t∈Ico a b,HasDerivWithinAt y (P t*((q t)^2-2*y t)) (Ici t) t)
    (hzd : ∀ t∈Ico a b,HasDerivWithinAt z (Q t*((q t)^2-2*z t)) (Ici t) t)
    (hK : 1≤K) (hP : ∀ t∈Ico a b,0≤P t)
    (hz0 : ∀ t∈Ico a b,0≤z t) (hz2 : ∀ t∈Ico a b,z t≤(q t)^2/2)
    (hPQ : ∀ t∈Ico a b,|P t-Q t|≤(K-1)*Q t)
    (h0 : |y a-z a|≤(K-1)*z a) {t : ℝ} (ht : t∈Icc a b) :
    |y t-z t|≤(K-1)*z t := by
  -- Use the identities/estimates `«2610.05164v2».Numerics.dissipative_abs_barrier` with the
  -- arguments shown in the proof.
  apply «2610.05164v2».Numerics.dissipative_abs_barrier (e:=fun x => y x-z x)
    (c:=fun x => -2*P x) (d:=fun x => (P x-Q x)*((q x)^2-2*z x))
    (g:=fun x => (K-1)*z x) (g':=fun x => (K-1)*Q x*((q x)^2-2*z x))
    (hy.sub hz) (hz.const_mul (K-1))
  · intro x hx
    convert! (hyd x hx).sub (hzd x hx) using 1
    ring
  · intro x hx
    convert! (hzd x hx).const_mul (K-1) using 1
    ring
  · intro x hx
    exact mul_nonpos_of_nonpos_of_nonneg (by norm_num) (hP x hx)
  · intro x hx
    exact mul_nonneg (sub_nonneg.mpr hK) (hz0 x hx)
  · intro x hx
    have hn : 0≤(q x)^2-2*z x := by linarith [hz2 x hx]
    rw [abs_mul,abs_of_nonneg hn]
    exact mul_le_mul_of_nonneg_right (hPQ x hx) hn
  · exact h0
  · exact ht

/--
Defines `linearDefect` of type `ℝ` by `t^3-linearFilter hφ κ t`.

Use: `«2610.05164v2».Primal.linearDefect_ode` rewrites with this definition to establish the
derivative within the stated domain: `HasDerivWithinAt (linearDefect hφ κ) (normalizedVelocity
φ t*((t^3)^2-2*linearDefect hφ κ t)) (Icc (0:ℝ) 1) t`.

Article: 2610.05164v2, Theorem 5.2 via `«2610.05164v2».Primal.familyConstraintMap_c1`.
-/
def linearDefect {φ : ℝ → ℝ} (hφ : Continuous φ) (κ t : ℝ) : ℝ :=
  t^3-linearFilter hφ κ t

/--
The derivative within the stated domain: `HasDerivWithinAt (linearDefect hφ κ)
(normalizedVelocity φ t*((t^3)^2-2*linearDefect hφ κ t)) (Icc (0:ℝ) 1) t`.

Use: `«2610.05164v2».Primal.linearFilter_parameter_bound` uses this derivative formula to
establish the stated quantitative bound `|linearFilter hφ κ t-linearFilter hψ κ t|≤(exp
d-1)*linearDefect hψ κ t`.

Article: 2610.05164v2, Theorem 5.2 via `«2610.05164v2».Primal.familyConstraintMap_c1`.

Proof: Use the identities/estimates `«2610.05164v2».Primal.linearFilter_regular_ode` with the
arguments shown in the proof.
-/
theorem linearDefect_ode {φ : ℝ → ℝ} (hφ : Continuous φ) {κ t : ℝ}
    (hκ : 0<κ) (ht : t∈Icc (0:ℝ) 1) :
    HasDerivWithinAt (linearDefect hφ κ)
      (normalizedVelocity φ t*((t^3)^2-2*linearDefect hφ κ t)) (Icc (0:ℝ) 1) t := by
  convert! ((hasDerivAt_id t).pow 3).hasDerivWithinAt.sub (linearFilter_regular_ode hφ hκ ht) using 1
  simp only [linearDefect,id_eq,Nat.cast_ofNat]
  ring

/--
The stated quantitative bound `|linearFilter hφ κ t-linearFilter hψ κ t|≤(exp d-1)*linearDefect
hψ κ t`.

Use: `«2610.05164v2».Primal.reflectedLinearFilter_parameter_bound` uses this bound to establish
the stated quantitative bound `|reflectedLinearFilter hφ κ t-reflectedLinearFilter hψ κ t|≤
(exp d-1)*(2-t^3-reflectedLinearFilter hψ κ t)`.

Article: 2610.05164v2, Theorem 5.2 via `«2610.05164v2».Primal.familyConstraintMap_c1`.

Proof: Use the identities/estimates `«2610.05164v2».Primal.linearFilter_continuous`,
`«2610.05164v2».Primal.linear_defect_comparison`, `«2610.05164v2».Primal.linearDefect_ode` with
the arguments shown in the proof.
-/
theorem linearFilter_parameter_bound {φ ψ : ℝ → ℝ}
    (hφ : Continuous φ) (hψ : Continuous ψ) {κ d t : ℝ} (hκ : 0<κ) (hd : 0≤d)
    (hprofile : ∀ x∈Icc (0:ℝ) 1,|φ x-ψ x|≤d) (ht : t∈Icc (0:ℝ) 1) :
    |linearFilter hφ κ t-linearFilter hψ κ t|≤(exp d-1)*linearDefect hψ κ t := by
  -- Establish continuity hy before using the function at limits or in calculus arguments.
  have hy : Continuous (linearDefect hφ κ) :=
    (continuous_id.pow 3).sub (linearFilter_continuous hφ hκ)
  -- Establish continuity hz before using the function at limits or in calculus arguments.
  have hz : Continuous (linearDefect hψ κ) :=
    (continuous_id.pow 3).sub (linearFilter_continuous hψ hκ)
  have h := linear_defect_comparison hy.continuousOn hz.continuousOn
    (y:=linearDefect hφ κ) (z:=linearDefect hψ κ)
    (P:=normalizedVelocity φ) (Q:=normalizedVelocity ψ) (q:=fun x => x^3) (K:=exp d)
    (a:=(0:ℝ)) (b:=1) ?_ ?_ (one_le_exp_iff.mpr hd) ?_ ?_ ?_ ?_ ?_ ht
  · simpa only [linearDefect,sub_sub_sub_cancel_left,abs_sub_comm] using h
  · intro x hx
    exact (linearDefect_ode hφ hκ ⟨hx.1,hx.2.le⟩).mono_of_mem_nhdsWithin
      (Filter.mem_of_superset (Icc_mem_nhdsGE hx.2) (fun z hz => ⟨hx.1.trans hz.1,hz.2⟩))
  · intro x hx
    exact (linearDefect_ode hψ hκ ⟨hx.1,hx.2.le⟩).mono_of_mem_nhdsWithin
      (Filter.mem_of_superset (Icc_mem_nhdsGE hx.2) (fun z hz => ⟨hx.1.trans hz.1,hz.2⟩))
  · intro x _
    unfold normalizedVelocity
    positivity
  · intro x hx
    exact sub_nonneg.mpr (linearFilter_bound hψ hκ ⟨hx.1,hx.2.le⟩)
  · intro x hx
    have hl := linearFilter_lower hψ hκ ⟨hx.1,hx.2.le⟩
    dsimp only [linearDefect]
    nlinarith
  · intro x hx
    exact normalizedVelocity_difference hd (hprofile x ⟨hx.1,hx.2.le⟩)
  · simp [linearDefect,linearFilter_initial]

/--
Defines `rightLinearDefect` of type `ℝ` by `2-(2-v)^3-rightLinearFilter hφ κ v`.

Use: `«2610.05164v2».Primal.reflectedLinearFilter_parameter_bound` uses this definition to
establish the stated quantitative bound `|reflectedLinearFilter hφ κ t-reflectedLinearFilter hψ
κ t|≤ (exp d-1)*(2-t^3-reflectedLinearFilter hψ κ t)`.

Article: 2610.05164v2, Theorem 5.2 via `«2610.05164v2».Primal.familyConstraintMap_c1`.
-/
def rightLinearDefect {φ : ℝ → ℝ} (hφ : Continuous φ) (κ v : ℝ) : ℝ :=
  2-(2-v)^3-rightLinearFilter hφ κ v

/--
The derivative within the stated domain: `HasDerivWithinAt (rightLinearDefect hφ κ)
(normalizedVelocity φ (2-v)*((2-(2-v)^3)^2-2*rightLinearDefect hφ κ v)) (Icc (1:ℝ) 2) v`.

Use: `«2610.05164v2».Primal.reflectedLinearFilter_parameter_bound` uses this derivative formula
to prove the bound `|reflectedLinearFilter hφ κ t-reflectedLinearFilter
hψ κ t|≤ (exp d-1)*(2-t^3-reflectedLinearFilter hψ κ t)`.

Article: 2610.05164v2, Theorem 5.2 via `«2610.05164v2».Primal.familyConstraintMap_c1`.

Proof: Use the identities/estimates `«2610.05164v2».Primal.rightLinearFilter_regular_ode` with
the arguments shown in the proof.
-/
theorem rightLinearDefect_ode {φ : ℝ → ℝ} (hφ : Continuous φ) {κ v : ℝ}
    (hκ : 0<κ) (hv : v∈Icc (1:ℝ) 2) :
    HasDerivWithinAt (rightLinearDefect hφ κ)
      (normalizedVelocity φ (2-v)*((2-(2-v)^3)^2-2*rightLinearDefect hφ κ v))
        (Icc (1:ℝ) 2) v := by
  -- Use the identities/estimates `«2610.05164v2».Primal.rightLinearFilter_regular_ode` with
  -- the arguments shown in the proof.
  have hq := (((hasDerivAt_id v).const_sub 2).pow 3).const_sub 2
  convert! hq.hasDerivWithinAt.sub (rightLinearFilter_regular_ode hφ hκ hv) using 1
  simp only [rightLinearDefect,id_eq,Nat.cast_ofNat]
  ring

/--
The stated quantitative bound `|reflectedLinearFilter hφ κ t-reflectedLinearFilter hψ κ t|≤
(exp d-1)*(2-t^3-reflectedLinearFilter hψ κ t)`.

Use: `«2610.05164v2».Primal.familyLinearFilter_parameter_bound` uses this bound to establish
the stated quantitative bound `|familyLinearFilter hψ hθ κ reflected a t-familyLinearFilter hψ
hθ κ reflected b t|≤ 2*(exp (‖a-b‖*∑ i,‖unitDirection (hθ i)‖)-1)`.

Article: 2610.05164v2, Theorem 5.2 via `«2610.05164v2».Primal.familyConstraintMap_c1`.

Proof: Use the identities/estimates `«2610.05164v2».Primal.reflectedLinearFilter_continuous`,
`«2610.05164v2».Primal.linearFilter_parameter_bound`, `«2610.05164v2».Primal.linearFilter_join`
with the arguments shown in the proof.
-/
theorem reflectedLinearFilter_parameter_bound {φ ψ : ℝ → ℝ}
    (hφ : Continuous φ) (hψ : Continuous ψ) {κ d t : ℝ} (hκ : 0<κ) (hd : 0≤d)
    (hprofile : ∀ x∈Icc (0:ℝ) 1,|φ x-ψ x|≤d) (ht : t∈Icc (0:ℝ) 1) :
    |reflectedLinearFilter hφ κ t-reflectedLinearFilter hψ κ t|≤
      (exp d-1)*(2-t^3-reflectedLinearFilter hψ κ t) := by
  -- Use the identities/estimates `«2610.05164v2».Primal.reflectedLinearFilter_continuous`,
  -- `«2610.05164v2».Primal.linearFilter_parameter_bound`,
  -- `«2610.05164v2».Primal.linearFilter_join` with the arguments shown in the proof.
  have hchart (x : ℝ) (hx : x∈Ico (1:ℝ) 2) : 2-x∈Icc (0:ℝ) 1 :=
    ⟨by linarith [hx.2],by linarith [hx.1]⟩
  -- Establish continuity hy before using the function at limits or in calculus arguments.
  have hy : Continuous (rightLinearDefect hφ κ) := by
    -- Establish continuity h before using the function at limits or in calculus arguments.
    have h : Continuous (rightLinearFilter hφ κ) :=
      (reflectedLinearFilter_continuous hφ hκ).comp (continuous_const.sub continuous_id)
    unfold rightLinearDefect
    fun_prop
  -- Establish continuity hz before using the function at limits or in calculus arguments.
  have hz : Continuous (rightLinearDefect hψ κ) := by
    -- Establish continuity h before using the function at limits or in calculus arguments.
    have h : Continuous (rightLinearFilter hψ κ) :=
      (reflectedLinearFilter_continuous hψ hκ).comp (continuous_const.sub continuous_id)
    unfold rightLinearDefect
    fun_prop
  have h0 : |rightLinearDefect hφ κ 1-rightLinearDefect hψ κ 1|≤
      (exp d-1)*rightLinearDefect hψ κ 1 := by
    have h := linearFilter_parameter_bound hφ hψ hκ hd hprofile (t:=1) (by norm_num)
    dsimp only [linearDefect] at h
    rw [linearFilter_join,linearFilter_join] at h
    simpa only [rightLinearDefect,rightLinearFilter,
      show (2:ℝ)-1=1 from by norm_num,one_pow,sub_sub_sub_cancel_left,abs_sub_comm] using h
  have hv : 2-t∈Icc (1:ℝ) 2 := ⟨by linarith [ht.2],by linarith [ht.1]⟩
  have h := linear_defect_comparison hy.continuousOn hz.continuousOn
    (y:=rightLinearDefect hφ κ) (z:=rightLinearDefect hψ κ)
    (P:=fun x => normalizedVelocity φ (2-x)) (Q:=fun x => normalizedVelocity ψ (2-x))
    (q:=fun x => 2-(2-x)^3) (K:=exp d) (a:=(1:ℝ)) (b:=2)
    ?_ ?_ (one_le_exp_iff.mpr hd) ?_ ?_ ?_ ?_ h0 hv
  · simpa only [rightLinearDefect,rightLinearFilter,sub_sub_cancel,sub_sub_sub_cancel_left,abs_sub_comm] using h
  · intro x hx
    exact (rightLinearDefect_ode hφ hκ ⟨hx.1,hx.2.le⟩).mono_of_mem_nhdsWithin
      (Filter.mem_of_superset (Icc_mem_nhdsGE hx.2) (fun z hz => ⟨hx.1.trans hz.1,hz.2⟩))
  · intro x hx
    exact (rightLinearDefect_ode hψ hκ ⟨hx.1,hx.2.le⟩).mono_of_mem_nhdsWithin
      (Filter.mem_of_superset (Icc_mem_nhdsGE hx.2) (fun z hz => ⟨hx.1.trans hz.1,hz.2⟩))
  · intro x _
    unfold normalizedVelocity
    positivity
  · intro x hx
    exact sub_nonneg.mpr (reflectedLinearFilter_bound hψ hκ (hchart x hx))
  · intro x hx
    have hl := reflectedLinearFilter_lower hψ hκ (hchart x hx)
    dsimp only [rightLinearDefect,rightLinearFilter]
    nlinarith
  · intro x hx
    exact normalizedVelocity_difference hd (hprofile (2-x) (hchart x hx))

end
end «2610.05164v2».Primal
