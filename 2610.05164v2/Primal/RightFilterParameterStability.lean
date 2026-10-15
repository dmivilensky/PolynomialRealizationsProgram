import «2610.05164v2».Primal.FilterParameterStability

/-!
Article: 2610.05164v2, Proposition 13.
Parameter comparison on the second half in forward time.
Use: `«2610.05164v2».Primal.reflectedNonlinearFilter_parameter_enclosed` feeds
`«2610.05164v2».Primal.familyNonlinearFilter_parameter_bound` (family Nonlinear Filter parameter
bound).
Proof chain: `«2610.05164v2».Primal.familyConstraintMap_c1` — 2610.05164v2, Theorem 5.2; Contraction
implies exact feasible density, uniqueness, iteration error and energy bound.
-/
namespace «2610.05164v2».Primal
noncomputable section
open Set Real
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/--
Defines `rightNonlinearFilter` of type `ℝ` by `reflectedNonlinearFilter hφ κ s (2-v)`.

Use: `«2610.05164v2».Primal.reflectedNonlinearFilter_parameter_enclosed` rewrites with this
definition to prove the bound `exp (-d)*(1+reflectedNonlinearFilter hψ
κ s t)≤1+reflectedNonlinearFilter hφ κ s t ∧ 1+reflectedNonlinearFilter hφ κ s t≤exp
d*(1+reflectedNonlinearFilter hψ κ s t)`.

Article: 2610.05164v2, Theorem 5.2 via `«2610.05164v2».Primal.familyConstraintMap_c1`.
-/
def rightNonlinearFilter {φ : ℝ → ℝ} (hφ : Continuous φ) (κ s v : ℝ) : ℝ :=
  reflectedNonlinearFilter hφ κ s (2-v)

/--
The derivative within the stated domain: `HasDerivWithinAt (fun v => 1+rightNonlinearFilter hφ
κ s v) (3*(s/κ)*(2-v)^2+(1+(s/κ)*(2-v)^3*(2-(2-v)^3))*normalizedVelocity φ (2-v)-
normalizedVelocity φ (2-v)*(1+rightNonlinearFilter hφ κ s v)^2) (Icc (1:ℝ) 2) v`.

Use: `«2610.05164v2».Primal.rightNonlinearFilter_parameter_upper` uses this derivative formula
to prove the bound `1+rightNonlinearFilter hφ κ s v≤exp
d*(1+rightNonlinearFilter hψ κ s v)`.

Article: 2610.05164v2, Theorem 5.2 via `«2610.05164v2».Primal.familyConstraintMap_c1`.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem right_shifted_nonlinear_ode {φ : ℝ → ℝ} (hφ : Continuous φ)
    {κ s v : ℝ} (hκ : 0<κ) (hs : 0≤s) (hv : v∈Icc (1:ℝ) 2) :
    HasDerivWithinAt (fun v => 1+rightNonlinearFilter hφ κ s v)
      (3*(s/κ)*(2-v)^2+(1+(s/κ)*(2-v)^3*(2-(2-v)^3))*normalizedVelocity φ (2-v)-
        normalizedVelocity φ (2-v)*(1+rightNonlinearFilter hφ κ s v)^2) (Icc (1:ℝ) 2) v := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  have ht : 2-v∈Icc (0:ℝ) 1 := by constructor <;> linarith [hv.1,hv.2]
  have h := (reflectedNonlinearFilter_ode hφ hκ hs ht).comp v
    ((hasDerivWithinAt_id v (Icc (1:ℝ) 2)).const_sub 2) (by
      intro x hx
      constructor <;> linarith [hx.1,hx.2])
  convert! h.const_add 1 using 1
  simp only [rightNonlinearFilter,normalizedVelocity,normalizedDensity]
  rw [exp_neg]
  field_simp [hκ.ne',exp_ne_zero]
  ring

/--
The stated quantitative bound `1+rightNonlinearFilter hφ κ s v≤exp d*(1+rightNonlinearFilter hψ
κ s v)`.

Use: `«2610.05164v2».Primal.reflectedNonlinearFilter_parameter_enclosed` uses this bound to
establish the stated quantitative bound `exp (-d)*(1+reflectedNonlinearFilter hψ κ s
t)≤1+reflectedNonlinearFilter hφ κ s t ∧ 1+reflectedNonlinearFilter hφ κ s t≤exp
d*(1+reflectedNonlinearFilter hψ κ s t)`.

Article: 2610.05164v2, Theorem 5.2 via `«2610.05164v2».Primal.familyConstraintMap_c1`.

Proof: Use the identities/estimates
`«2610.05164v2».Primal.reflectedNonlinearFilter_continuous`,
`«2610.05164v2».Primal.scaled_riccati_comparison`,
`«2610.05164v2».Primal.right_shifted_nonlinear_ode` with the arguments shown in the proof.
-/
theorem rightNonlinearFilter_parameter_upper {φ ψ : ℝ → ℝ}
    (hφ : Continuous φ) (hψ : Continuous ψ) {κ s d : ℝ}
    (hκ : 0<κ) (hs : 0≤s) (hd : 0≤d)
    (hprofile : ∀ t∈Icc (0:ℝ) 1,|φ t-ψ t|≤d)
    {v : ℝ} (hv : v∈Icc (1:ℝ) 2) :
    1+rightNonlinearFilter hφ κ s v≤exp d*(1+rightNonlinearFilter hψ κ s v) := by
  -- Use the identities/estimates `«2610.05164v2».Primal.reflectedNonlinearFilter_continuous`,
  -- `«2610.05164v2».Primal.scaled_riccati_comparison`,
  -- `«2610.05164v2».Primal.right_shifted_nonlinear_ode` with the arguments shown in the proof.
  let A := fun v:ℝ => 3*(s/κ)*(2-v)^2
  let c := fun v:ℝ => 1+(s/κ)*(2-v)^3*(2-(2-v)^3)
  have hchart (x : ℝ) (hx : x∈Ico (1:ℝ) 2) : 2-x∈Icc (0:ℝ) 1 :=
    ⟨by linarith [hx.2],by linarith [hx.1]⟩
  -- Establish continuity hleft before using the function at limits or in calculus arguments.
  have hleft : Continuous (rightNonlinearFilter hφ κ s) :=
    (reflectedNonlinearFilter_continuous hφ hκ hs).comp (continuous_const.sub continuous_id)
  -- Establish continuity hright before using the function at limits or in calculus arguments.
  have hright : Continuous (rightNonlinearFilter hψ κ s) :=
    (reflectedNonlinearFilter_continuous hψ hκ hs).comp (continuous_const.sub continuous_id)
  apply scaled_riccati_comparison (hleft.const_add 1).continuousOn
    (hright.const_add 1).continuousOn (A:=A) (c:=c)
    (P:=fun x => normalizedVelocity φ (2-x)) (Q:=fun x => normalizedVelocity ψ (2-x))
  · intro x hx
    exact (right_shifted_nonlinear_ode hφ hκ hs ⟨hx.1,hx.2.le⟩).mono_of_mem_nhdsWithin
      (Filter.mem_of_superset (Icc_mem_nhdsGE hx.2) (fun z hz => ⟨hx.1.trans hz.1,hz.2⟩))
  · intro x hx
    exact (right_shifted_nonlinear_ode hψ hκ hs ⟨hx.1,hx.2.le⟩).mono_of_mem_nhdsWithin
      (Filter.mem_of_superset (Icc_mem_nhdsGE hx.2) (fun z hz => ⟨hx.1.trans hz.1,hz.2⟩))
  · exact one_le_exp_iff.mpr hd
  · intro x _
    dsimp [A]
    positivity
  · intro x hx
    have ht := hchart x hx
    have ht3 : (2-x)^3≤1 := pow_le_one₀ ht.1 ht.2
    have hh : 0≤2-(2-x)^3 := by linarith
    exact add_nonneg zero_le_one (mul_nonneg
      (mul_nonneg (div_nonneg hs hκ.le) (pow_nonneg ht.1 _)) hh)
  · intro x _
    unfold normalizedVelocity
    positivity
  · intro x hx
    exact normalizedVelocity_comparison (hprofile (2-x) (hchart x hx))
  · intro x hx
    apply normalizedVelocity_comparison
    simpa only [abs_sub_comm] using hprofile (2-x) (hchart x hx)
  · intro x _
    exact add_nonneg (by norm_num) (reflectedNonlinearFilter_nonneg hψ hκ hs (2-x))
  · have h := nonlinearFilter_parameter_upper hφ hψ hκ hs hd hprofile (t:=1) (by norm_num)
    rw [nonlinearFilter_join,nonlinearFilter_join] at h
    simpa only [rightNonlinearFilter,show (2:ℝ)-1=1 from by norm_num] using h
  · exact hv

/--
Both bounds hold at every point of the reflected chart, including the physical right endpoint.
The two sides use the same parameter deviation.

The stated quantitative bound `exp (-d)*(1+reflectedNonlinearFilter hψ κ s
t)≤1+reflectedNonlinearFilter hφ κ s t ∧ 1+reflectedNonlinearFilter hφ κ s t≤exp
d*(1+reflectedNonlinearFilter hψ κ s t)`.

Use: `«2610.05164v2».Primal.familyNonlinearFilter_parameter_bound` uses this bound to establish
the stated quantitative bound `|familyNonlinearFilter hψ hθ κ s reflected a
t-familyNonlinearFilter hψ hθ κ s reflected b t|≤ (exp (‖a-b‖*∑ i,‖unitDirection (hθ
i)‖)-1)*(1+2*s/κ)`.

Article: 2610.05164v2, Theorem 5.2 via `«2610.05164v2».Primal.familyConstraintMap_c1`.

Proof: Use the identities/estimates
`«2610.05164v2».Primal.rightNonlinearFilter_parameter_upper` with the arguments shown in the
proof.
-/
theorem reflectedNonlinearFilter_parameter_enclosed {φ ψ : ℝ → ℝ}
    (hφ : Continuous φ) (hψ : Continuous ψ) {κ s d : ℝ}
    (hκ : 0<κ) (hs : 0≤s) (hd : 0≤d)
    (hprofile : ∀ t∈Icc (0:ℝ) 1,|φ t-ψ t|≤d)
    {t : ℝ} (ht : t∈Icc (0:ℝ) 1) :
    exp (-d)*(1+reflectedNonlinearFilter hψ κ s t)≤1+reflectedNonlinearFilter hφ κ s t ∧
    1+reflectedNonlinearFilter hφ κ s t≤exp d*(1+reflectedNonlinearFilter hψ κ s t) := by
  -- Use the identities/estimates `«2610.05164v2».Primal.rightNonlinearFilter_parameter_upper`
  -- with the arguments shown in the proof.
  have hv : 2-t∈Icc (1:ℝ) 2 := ⟨by linarith [ht.2],by linarith [ht.1]⟩
  have hu := rightNonlinearFilter_parameter_upper hφ hψ hκ hs hd hprofile hv
  have hl := rightNonlinearFilter_parameter_upper hψ hφ hκ hs hd
    (fun x hx => by simpa only [abs_sub_comm] using hprofile x hx) hv
  simp only [rightNonlinearFilter,sub_sub_cancel] at hu hl
  refine ⟨?_,hu⟩
  rw [exp_neg]
  exact (inv_mul_le_iff₀ (exp_pos d)).mpr hl

end
end «2610.05164v2».Primal
