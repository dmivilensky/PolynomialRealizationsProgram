import nesterov.TwoStep.BoundaryQuadratic
import nesterov.TwoStep.LagScaled

/-! Article: Proposition `prop:boundary`, the strict lag-one certificate,
with both finite and infinite scaled margins. -/
namespace nesterov.TwoStep
noncomputable section
open Filter Set
open scoped Topology

theorem scaled_tail_two_exact (ε c θ y τ : ℝ) :
    2*scaledTail ε c θ y τ 2=
      (2-c*ε)*realCharacteristic (1-θ*ε) τ y (ε^2) (-(1-c*ε))*
        realCharacteristic (1-θ*ε) τ y 1 (-(1-c*ε))-scaledP0 ε c θ y τ := by
  unfold scaledTail scaledP0 scaledP1 scaledP2 scaledP3 P0 P1 P2 P3 E0 E1 E2 realCharacteristic
  ring

private theorem concave_quadratic_positive {a b d : ℝ} (h0 : 0<a) (h2 : 0<a+2*b+4*d)
    (hd : d≤0) {ξ : ℝ} (hξ : ξ∈Icc (0:ℝ) 2) : 0<a+b*ξ+d*ξ^2 := by
  rcases hξ.2.lt_or_eq with hlt|rfl
  · have hp : 0<(1-ξ/2)*a+(ξ/2)*(a+2*b+4*d) :=
      add_pos_of_pos_of_nonneg (mul_pos (by linarith) h0)
        (mul_nonneg (by positivity [hξ.1]) h2.le)
    have hr : 0≤ -d*(ξ*(2-ξ)) :=
      mul_nonneg (neg_nonneg.mpr hd) (mul_nonneg hξ.1 (by linarith))
    nlinarith only [hp,hr]
  · nlinarith only [h2]

namespace Scaling
variable {A : Type*} {l : Filter A} {θ y τ : ℝ} (F : Scaling A l θ y τ)

private theorem boundary_tail_positive {c : ℝ} (hct : c<θ/3) (hτ : 1/2<τ)
    (hboundary : y*(1+2*τ)=4)
    (hminus : ∃ d : ℝ,0<d ∧ ∀ᶠ a in l,d≤realCharacteristic (F.tuning a).beta
      (F.tuning a).tau (F.tuning a).stepSize 1 (-(1-c*F.epsilon a))/F.epsilon a) :
    ∀ᶠ a in l,∀ ξ∈Icc (0:ℝ) 2,
      0<scaledTail (F.epsilon a) c (F.thetaAt a) (F.tuning a).stepSize (F.tuning a).tau ξ := by
  obtain ⟨d,hd,hminus⟩ := hminus
  have hp1 : 0<2*y*(θ-3*c) := mul_pos (mul_pos (by norm_num) F.step_pos) (by linarith)
  have hyτ : 1<τ*y := by
    have hp := mul_pos F.step_pos (sub_pos.mpr hτ)
    nlinarith
  have hp3 : 4*(1-τ*y)<0 := by linarith
  have hr : Tendsto (fun a=>1-c*F.epsilon a) l (𝓝 1) := by
    simpa using (tendsto_const_nhds (x:=(1:ℝ))).sub (F.epsilon_zero.const_mul c)
  filter_upwards [(F.P1_div_tendsto c).eventually (eventually_gt_nhds hp1),
    (F.P3_tendsto c).eventually (eventually_lt_nhds hp3),
    (F.P0_div_tendsto c).eventually (eventually_lt_nhds hd),
    (F.slow_negative_radius_tendsto c).eventually (eventually_gt_nhds (by norm_num : (2:ℝ)<4)),
    hr.eventually (eventually_gt_nhds (by norm_num : (0:ℝ)<1)),
    hminus,F.epsilon_pos,F.beta_eq] with a h1 h3 h0 hslow hr hminus he hb
  have h1p := (div_pos_iff_of_pos_right he).mp h1
  have h0p := (div_lt_iff₀ he).mp h0
  have hminus' := (le_div_iff₀ he).mp hminus
  have hL : 0<realCharacteristic (F.tuning a).beta (F.tuning a).tau (F.tuning a).stepSize
      1 (-(1-c*F.epsilon a)) := (mul_pos hd he).trans_le hminus'
  have hprod : d*F.epsilon a≤(2-c*F.epsilon a)*
      realCharacteristic (F.tuning a).beta (F.tuning a).tau (F.tuning a).stepSize
        (F.epsilon a^2) (-(1-c*F.epsilon a))*
      realCharacteristic (F.tuning a).beta (F.tuning a).tau (F.tuning a).stepSize
        1 (-(1-c*F.epsilon a)) := by
    have hfac : 1≤(2-c*F.epsilon a)*realCharacteristic (F.tuning a).beta
        (F.tuning a).tau (F.tuning a).stepSize (F.epsilon a^2) (-(1-c*F.epsilon a)) := by
      nlinarith
    exact hminus'.trans (le_mul_of_one_le_left hL.le hfac)
  have htwo : 0<scaledTail (F.epsilon a) c (F.thetaAt a) (F.tuning a).stepSize (F.tuning a).tau 2 := by
    have hh := scaled_tail_two_exact (F.epsilon a) c (F.thetaAt a) (F.tuning a).stepSize (F.tuning a).tau
    rw [hb] at hprod
    nlinarith only [hh,h0p,hprod]
  intro ξ hξ
  exact concave_quadratic_positive h1p
    (by simpa only [scaledTail,show (2:ℝ)^2=4 by norm_num,mul_comm] using htwo) h3.le hξ

/-- The literal lag-one upper bound on the stability boundary, finite cπ. -/
theorem boundary_lagOne_upper {s c : ℝ} (hc0 : 0<c) (hc : c<Flow.cF θ y)
    (hτ : 1/2<τ) (hboundary : y*(1+2*τ)=4)
    (hs : Tendsto F.stabilityMargin l (𝓝 s)) (hcp : c<alternatingConstant θ τ s) :
    ∀ᶠ a in l,Momentum.momentumRate (F.tuning a).beta (F.tuning a).tau (F.tuning a).stepSize
      (F.tuning a).step_pos.ne' (F.epsilon a^2) 1<1-c*F.epsilon a := by
  have hid := alternatingConstant_identity (θ:=θ) (s:=s) (by linarith : 0<τ) hboundary
  have hp : 0<s-2*θ-c*y*τ := by
    have hh := mul_lt_mul_of_pos_right hcp (mul_pos F.step_pos (by linarith : 0<τ))
    nlinarith
  have hminus : ∃ d : ℝ,0<d ∧ ∀ᶠ a in l,d≤realCharacteristic (F.tuning a).beta
      (F.tuning a).tau (F.tuning a).stepSize 1 (-(1-c*F.epsilon a))/F.epsilon a := by
    refine ⟨(s-2*θ-c*y*τ)/2,by linarith,?_⟩
    exact ((F.negative_radius_scaled_tendsto c hboundary hs).eventually
      (eventually_gt_nhds (by linarith : (s-2*θ-c*y*τ)/2<s-2*θ-c*y*τ))).mono fun _ ha=>ha.le
  exact (F.lag_scaled hc0 (lt_of_lt_of_le hc (min_le_right _ _))
    (F.boundary_tail_positive (lt_of_lt_of_le hc (min_le_left _ _)) hτ hboundary hminus)).mono fun _ ha=>ha.2.2

/-- The same upper certificate for an infinite scaled stability margin. -/
theorem boundary_lagOne_upper_infinite {c : ℝ} (hc0 : 0<c) (hc : c<Flow.cF θ y)
    (hτ : 1/2<τ) (hboundary : y*(1+2*τ)=4) (hs : Tendsto F.stabilityMargin l atTop) :
    ∀ᶠ a in l,Momentum.momentumRate (F.tuning a).beta (F.tuning a).tau (F.tuning a).stepSize
      (F.tuning a).step_pos.ne' (F.epsilon a^2) 1<1-c*F.epsilon a := by
  have hminus : ∃ d : ℝ,0<d ∧ ∀ᶠ a in l,d≤realCharacteristic (F.tuning a).beta
      (F.tuning a).tau (F.tuning a).stepSize 1 (-(1-c*F.epsilon a))/F.epsilon a :=
    ⟨1,by norm_num,(F.negative_radius_scaled_atTop c hs).eventually_ge_atTop 1⟩
  exact (F.lag_scaled hc0 (lt_of_lt_of_le hc (min_le_right _ _))
    (F.boundary_tail_positive (lt_of_lt_of_le hc (min_le_left _ _)) hτ hboundary hminus)).mono fun _ ha=>ha.2.2

end Scaling
end
end nesterov.TwoStep
