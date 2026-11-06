import nesterov.Slow.Continuity

/-! The actual moving near-one factor and its coefficient limits. -/
namespace nesterov.Slow.SecondOrderFamily
noncomputable section
open Polynomial Filter Set
open scoped Topology
variable {θ y : ℝ} (F : nesterov.Slow.SecondOrderFamily θ y)

theorem beta_tendsto : Tendsto F.beta (𝓝[>] (0:ℝ)) (𝓝 1) := by
  have hε : Tendsto (fun ε : ℝ=>ε) (𝓝[>] (0:ℝ)) (𝓝 0) := continuous_id.continuousWithinAt.tendsto
  have he : (fun ε : ℝ=>1-ε*F.thetaAt ε)=ᶠ[𝓝[>] (0:ℝ)] F.beta := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hn : ε≠0 := ne_of_gt hε
    dsimp [thetaAt]
    field_simp
    ring
  have hh := (tendsto_const_nhds.sub (hε.mul F.thetaAt_tendsto)).congr' he
  simpa using hh

theorem beta_ne_one : ∀ᶠ ε in 𝓝[>] (0:ℝ),F.beta ε≠1 := by
  have hp := F.thetaAt_tendsto.eventually (eventually_gt_nhds F.theta_pos)
  filter_upwards [hp] with ε hε hβ
  have hz : F.thetaAt ε=0 := by simp [thetaAt,hβ]
  rw [hz] at hε
  exact lt_irrefl _ hε

theorem quotient_zero : F.quotient 0=F.q0 := by
  unfold quotient
  change (F.method 0).recurrencePolynomial /ₘ (X-C 1) /ₘ (X-C (F.beta 0))=F.q0
  rw [F.beta_zero,F.initial_factor,pow_two,mul_assoc,
    mul_divByMonic_cancel_left _ (monic_X_sub_C 1),
    mul_divByMonic_cancel_left _ (monic_X_sub_C 1)]

theorem factorization : ∀ᶠ ε in 𝓝[>] (0:ℝ),
    F.v ε=(X-C 1)*(X-C (F.beta ε))*F.quotient ε := by
  filter_upwards [F.beta_root,F.beta_ne_one] with ε hroot hne
  have hfirst : (X-C 1)*(F.v ε /ₘ (X-C 1))=F.v ε :=
    mul_divByMonic_eq_iff_isRoot.mpr (F.v_one ε)
  have hb : (F.v ε /ₘ (X-C 1)).eval (F.beta ε)=0 := by
    have hh := congrArg (Polynomial.eval (F.beta ε)) hfirst
    simp only [eval_mul,eval_sub,eval_X,eval_C,hroot] at hh
    exact (mul_eq_zero.mp hh).resolve_left (sub_ne_zero.mpr hne)
  have hsecond : (X-C (F.beta ε))*F.quotient ε=F.v ε /ₘ (X-C 1) :=
    mul_divByMonic_eq_iff_isRoot.mpr hb
  rw [←hfirst,←hsecond]
  ring

theorem quotient_natDegree_le (ε : ℝ) : (F.quotient ε).natDegree≤F.memory := by
  unfold quotient
  rw [natDegree_divByMonic _ (monic_X_sub_C _),natDegree_divByMonic _ (monic_X_sub_C _),
    natDegree_X_sub_C,natDegree_X_sub_C,F.v_natDegree]
  omega

theorem quotient_coeff_tendsto (j : ℕ) :
    Tendsto (fun ε=>(F.quotient ε).coeff j) (𝓝[>] (0:ℝ)) (𝓝 (F.q0.coeff j)) := by
  have hfirst (n : ℕ) : Tendsto (fun ε=>(F.v ε /ₘ (X-C 1)).coeff n)
      (𝓝[>] (0:ℝ)) (𝓝 ((F.v 0 /ₘ (X-C 1)).coeff n)) :=
    nesterov.Slow.tendsto_divByMonic_coeff F.v_coeff_tendsto
      (fun ε=>(F.v_natDegree ε).le) (F.v_natDegree 0).le tendsto_const_nhds n
  have hdeg (ε : ℝ) : (F.v ε /ₘ (X-C 1)).natDegree≤F.memory := by
    rw [natDegree_divByMonic _ (monic_X_sub_C 1),natDegree_X_sub_C,F.v_natDegree]
    omega
  have hh := nesterov.Slow.tendsto_divByMonic_coeff hfirst hdeg (hdeg 0) F.beta_tendsto j
  change Tendsto (fun ε=>(F.quotient ε).coeff j) _
    (𝓝 (((F.v 0 /ₘ (X-C 1)) /ₘ (X-C 1)).coeff j)) at hh
  have hq : (F.v 0 /ₘ (X-C 1)) /ₘ (X-C 1)=F.q0 := by
    simpa only [quotient,F.beta_zero] using F.quotient_zero
  rwa [hq] at hh

theorem quotient_eval_tendsto {z : ℝ→ℂ} {z₀ : ℂ}
    (hz : Tendsto z (𝓝[>] (0:ℝ)) (𝓝 z₀)) :
    Tendsto (fun ε=>(F.quotient ε).eval₂ Complex.ofRealHom (z ε))
      (𝓝[>] (0:ℝ)) (𝓝 (F.q0.eval₂ Complex.ofRealHom z₀)) := by
  apply nesterov.Slow.tendsto_eval₂_of_coeff F.quotient_coeff_tendsto
    (fun ε=>lt_of_le_of_lt (F.quotient_natDegree_le ε) (Nat.lt_succ_self _))
    _ hz
  rw [←F.quotient_zero]
  exact lt_of_le_of_lt (F.quotient_natDegree_le 0) (Nat.lt_succ_self _)

theorem stepAt_tendsto : Tendsto F.stepAt (𝓝[>] (0:ℝ)) (𝓝 y) := by
  have hq : Tendsto (fun ε=>(F.quotient ε).eval 1) (𝓝[>] (0:ℝ)) (𝓝 (-1/y)) := by
    have hh := F.quotient_eval_tendsto (z:=fun _=>(1:ℂ)) tendsto_const_nhds
    have hr := Complex.continuous_re.tendsto _ |>.comp hh
    have he (p : Polynomial ℝ) : p.eval₂ Complex.ofRealHom 1=((p.eval (1:ℝ):ℝ):ℂ) := by
      exact eval₂_at_apply (p:=p) Complex.ofRealHom (1:ℝ)
    simpa only [Function.comp_def,he,Complex.ofReal_re,F.q0_one] using hr
  have hn : (-1/y:ℝ)≠0 := div_ne_zero (by norm_num) (ne_of_gt F.step_pos)
  have hh : Tendsto (fun ε=>(-1:ℝ)/(F.quotient ε).eval 1) (𝓝[>] (0:ℝ))
      (𝓝 ((-1:ℝ)/(-1/y))) := tendsto_const_nhds.div hq hn
  have he : (-1:ℝ)/(-1/y)=y := by field_simp
  change Tendsto (fun ε=>(-1:ℝ)/(F.quotient ε).eval 1) _ _
  rwa [he] at hh

end
end nesterov.Slow.SecondOrderFamily
