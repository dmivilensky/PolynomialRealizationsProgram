import nesterov.TwoStep.AlternatingAsymptotics

/-! The upper-endpoint Jury test and the exact quadratic boundary constant,
including an infinite stability margin. -/
namespace nesterov.TwoStep
noncomputable section
open Filter Set
open scoped Topology
namespace Scaling
variable {A : Type*} {l : Filter A} {θ y τ : ℝ} (F : Scaling A l θ y τ)

theorem negative_radius_scaled_exact (c : ℝ) : ∀ᶠ a in l,
    realCharacteristic (F.tuning a).beta (F.tuning a).tau (F.tuning a).stepSize
      1 (-(1-c*F.epsilon a))/F.epsilon a=
      F.stabilityMargin a-2*F.thetaAt a+c*((F.tuning a).stepSize*(1+(F.tuning a).tau)-4)+
        F.epsilon a*(c^2+c*F.thetaAt a) := by
  filter_upwards [F.epsilon_pos,F.beta_eq] with a ha hb
  rw [hb]
  unfold realCharacteristic Quadratic.S Quadratic.Q stabilityMargin
  field_simp
  ring

theorem negative_radius_remainder_tendsto (c : ℝ) :
    Tendsto (fun a=> -2*F.thetaAt a+c*((F.tuning a).stepSize*(1+(F.tuning a).tau)-4)+
      F.epsilon a*(c^2+c*F.thetaAt a)) l (𝓝 (-2*θ+c*(y*(1+τ)-4))) := by
  have hh := ((F.theta_tendsto.const_mul (-2)).add
    (((F.step_tendsto.mul ((tendsto_const_nhds (x:=(1:ℝ))).add F.tau_tendsto)).sub_const 4).const_mul c)).add
      (F.epsilon_zero.mul ((tendsto_const_nhds (x:=c^2)).add (F.theta_tendsto.const_mul c)))
  simpa only [zero_mul,mul_zero,add_zero,thetaAt,mul_comm] using hh

theorem negative_radius_scaled_tendsto {s : ℝ} (c : ℝ)
    (hboundary : y*(1+2*τ)=4) (hs : Tendsto F.stabilityMargin l (𝓝 s)) :
    Tendsto (fun a=>realCharacteristic (F.tuning a).beta (F.tuning a).tau
      (F.tuning a).stepSize 1 (-(1-c*F.epsilon a))/F.epsilon a)
      l (𝓝 (s-2*θ-c*y*τ)) := by
  have hh := hs.add (F.negative_radius_remainder_tendsto c)
  have he : s+(-2*θ+c*(y*(1+τ)-4))=s-2*θ-c*y*τ := by linear_combination c*hboundary
  rw [he] at hh
  apply hh.congr'
  filter_upwards [F.negative_radius_scaled_exact c] with a ha
  rw [ha]
  ring

theorem negative_radius_scaled_atTop (c : ℝ)
    (hs : Tendsto F.stabilityMargin l atTop) :
    Tendsto (fun a=>realCharacteristic (F.tuning a).beta (F.tuning a).tau
      (F.tuning a).stepSize 1 (-(1-c*F.epsilon a))/F.epsilon a) l atTop := by
  apply tendsto_atTop.mpr
  intro b
  have hr := (F.negative_radius_remainder_tendsto c).eventually
    (eventually_gt_nhds (show -2*θ+c*(y*(1+τ)-4)-1< -2*θ+c*(y*(1+τ)-4) by linarith))
  filter_upwards [hs.eventually_ge_atTop (b-(-2*θ+c*(y*(1+τ)-4))+1),hr,
    F.negative_radius_scaled_exact c] with a ha hb he
  rw [he]
  linarith

theorem alternatingConstant_identity {s : ℝ} (hτ : 0<τ) (hboundary : y*(1+2*τ)=4) :
    alternatingConstant θ τ s*(y*τ)=s-2*θ := by
  unfold alternatingConstant
  field_simp
  linear_combination (s-2*θ)*hboundary

theorem boundary_roots_eventually_lt {s c : ℝ} (hτ : 1/2≤τ)
    (hboundary : y*(1+2*τ)=4) (hs : Tendsto F.stabilityMargin l (𝓝 s))
    (hcq : c<Flow.cQ θ y) (hcp : c<alternatingConstant θ τ s) :
    ∀ᶠ a in l,∀ lam∈Icc (F.epsilon a^2) 1,∀ z : ℂ,
      Quadratic.characteristic (F.tuning a).beta (F.tuning a).tau (F.tuning a).stepSize lam z=0 →
        ‖z‖<1-c*F.epsilon a := by
  have hτp : 0<τ := by linarith
  have hid := alternatingConstant_identity (θ:=θ) (s:=s) hτp hboundary
  have hpos : 0<s-2*θ-c*y*τ := by
    have hh := mul_lt_mul_of_pos_right hcp (mul_pos F.step_pos hτp)
    nlinarith
  apply F.roots_eventually_lt_of_upper_endpoint hcq
  filter_upwards [(F.negative_radius_scaled_tendsto c hboundary hs).eventually (eventually_gt_nhds hpos),
    F.epsilon_pos] with a ha he
  exact (div_pos_iff_of_pos_right he).mp ha

theorem boundary_roots_eventually_lt_infinite {c : ℝ} (hs : Tendsto F.stabilityMargin l atTop)
    (hcq : c<Flow.cQ θ y) :
    ∀ᶠ a in l,∀ lam∈Icc (F.epsilon a^2) 1,∀ z : ℂ,
      Quadratic.characteristic (F.tuning a).beta (F.tuning a).tau (F.tuning a).stepSize lam z=0 →
        ‖z‖<1-c*F.epsilon a := by
  apply F.roots_eventually_lt_of_upper_endpoint hcq
  filter_upwards [(F.negative_radius_scaled_atTop c hs).eventually_gt_atTop 0,F.epsilon_pos]
    with a ha he
  exact (div_pos_iff_of_pos_right he).mp ha

private theorem rate_lt_of_root_bound {c : ℝ}
    (h : ∀ᶠ a in l,∀ lam∈Icc (F.epsilon a^2) 1,∀ z : ℂ,
      Quadratic.characteristic (F.tuning a).beta (F.tuning a).tau (F.tuning a).stepSize lam z=0 →
        ‖z‖<1-c*F.epsilon a) : ∀ᶠ a in l,F.rate a<1-c*F.epsilon a := by
  filter_upwards [h,F.epsilon_pos,F.epsilon_zero.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1))]
    with a ha he he1
  obtain ⟨lam,hlam,z,hz,hze⟩ := (Quadratic.quadraticRate_isGreatest_general
    (β:=(F.tuning a).beta) (τ:=(F.tuning a).tau) (h:=(F.tuning a).stepSize)
    (show F.epsilon a^2≤1 by nlinarith)).1
  change Quadratic.quadraticRate _ _ _ _ _<1-c*F.epsilon a
  rw [hze]
  exact ha lam hlam z hz

/-- Lemma quadboundary, finite alternating constant. -/
theorem quadratic_boundary_coefficient_tendsto {s : ℝ} (hτ : 1/2≤τ)
    (hboundary : y*(1+2*τ)=4) (hstable : ∀ᶠ a in l,(F.tuning a).Stable (F.epsilon a^2) 1)
    (hs : Tendsto F.stabilityMargin l (𝓝 s)) :
    Tendsto (fun a=>(1-F.rate a)/F.epsilon a) l
      (𝓝 (min (Flow.cQ θ y) (alternatingConstant θ τ s))) := by
  apply tendsto_order.mpr
  constructor
  · intro c hc
    have hh := F.rate_lt_of_root_bound (F.boundary_roots_eventually_lt hτ hboundary hs
      (lt_of_lt_of_le hc (min_le_left _ _)) (lt_of_lt_of_le hc (min_le_right _ _)))
    filter_upwards [hh,F.epsilon_pos] with a ha he
    apply (lt_div_iff₀ he).mpr
    linarith
  · intro b hb
    rcases le_total (Flow.cQ θ y) (alternatingConstant θ τ s) with hq|hp
    · rw [min_eq_left hq] at hb
      exact F.quadratic_coefficient_eventually_lt hb
    · rw [min_eq_right hp] at hb
      filter_upwards [(F.alternating_shift_scaled_tendsto hτ hboundary hstable hs).eventually (eventually_lt_nhds hb),
        F.alternating_rate_lower hτ hboundary hstable] with a ha hb
      exact hb.2.2.trans_lt ha

/-- Lemma quadboundary, infinite alternating constant. -/
theorem quadratic_boundary_coefficient_tendsto_infinite (hs : Tendsto F.stabilityMargin l atTop) :
    Tendsto (fun a=>(1-F.rate a)/F.epsilon a) l (𝓝 (Flow.cQ θ y)) := by
  apply tendsto_order.mpr
  constructor
  · intro c hc
    filter_upwards [F.rate_lt_of_root_bound (F.boundary_roots_eventually_lt_infinite hs hc),F.epsilon_pos]
      with a ha he
    apply (lt_div_iff₀ he).mpr
    linarith
  · exact fun b hb=>F.quadratic_coefficient_eventually_lt hb

end Scaling
end
end nesterov.TwoStep
