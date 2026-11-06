import nesterov.Layer.Coefficients

/-! The exact lag-one upper bound throughout the half-step layer. -/
namespace nesterov.Layer
noncomputable section

theorem quadratic_pos_of_discriminant {a b d z : ℝ} (hd : 0<d)
    (hdisc : b^2<4*a*d) : 0<a+b*z+d*z^2 := by
  have hp : 0<4*d*(a+b*z+d*z^2) := by nlinarith [sq_nonneg (2*d*z+b)]
  exact (mul_pos_iff_of_pos_left (by positivity : 0<4*d)).mp hp

end
end nesterov.Layer

namespace nesterov.TwoStep.Scaling
noncomputable section
open Filter Set
open scoped Topology
variable {A : Type*} {l : Filter A} {θ y : ℝ} (F : Scaling A l θ y (1/2))

def layerLowerMiddle (c : ℝ) (a : A) : ℝ :=
  -4*(F.tuning a).stepSize*max (F.layerDeficit a) 0-
    |Real.sqrt (F.epsilon a)*F.layerError c 1 a|

theorem layerLowerMiddle_le (c : ℝ) : ∀ᶠ a in l,
    F.layerLowerMiddle c a≤scaledP2 (F.epsilon a) c (F.thetaAt a)
      (F.tuning a).stepSize (F.tuning a).tau/Real.sqrt (F.epsilon a) := by
  filter_upwards [F.P2_layer_exact c] with a ha
  rw [ha]
  have hm := mul_le_mul_of_nonneg_left (le_max_left (F.layerDeficit a) 0)
    (mul_nonneg (show (0:ℝ)≤4 by norm_num) (F.tuning a).step_pos.le)
  have hab := neg_abs_le (Real.sqrt (F.epsilon a)*F.layerError c 1 a)
  unfold layerLowerMiddle
  linarith

theorem layerLowerMiddle_tendsto {B : ℝ} (c : ℝ)
    (hB : Tendsto (fun a=>max (F.layerDeficit a) 0) l (𝓝 B)) :
    Tendsto (F.layerLowerMiddle c) l (𝓝 (-4*y*B)) := by
  change Tendsto (fun a=> -4*(F.tuning a).stepSize*max (F.layerDeficit a) 0-
    |Real.sqrt (F.epsilon a)*F.layerError c 1 a|) l (𝓝 (-4*y*B))
  have ht := ((F.step_tendsto.const_mul (-4)).mul hB).sub
    ((F.sqrt_epsilon_tendsto.mul (F.layerError_tendsto c 1)).abs)
  simpa only [zero_mul,abs_zero,sub_zero] using ht

private theorem tail_pos_of_rescaled {ε s p₁ p₂ p₃ b ξ : ℝ}
    (hs : s^2=ε) (hsp : 0<s) (hd : 0<p₃)
    (hdisc : b^2<4*(p₁/ε)*p₃) (hbl : b≤p₂/s) (hξ : 0≤ξ) :
    0<p₁+p₂*ξ+p₃*ξ^2 := by
  have he : 0<ε := by rw [←hs];positivity
  have hp := Layer.quadratic_pos_of_discriminant (z:=ξ/s) hd hdisc
  have hm := mul_le_mul_of_nonneg_right hbl (div_nonneg hξ hsp.le)
  have hscaled : (p₁+p₂*ξ+p₃*ξ^2)/ε=p₁/ε+(p₂/s)*(ξ/s)+p₃*(ξ/s)^2 := by
    rw [←hs]
    field_simp
  have hp' : 0<(p₁+p₂*ξ+p₃*ξ^2)/ε := by rw [hscaled];linarith
  exact (div_pos_iff_of_pos_right he).mp hp'

/-- The upper proof only needs convergence of the positive deficit. This
also covers a deficit tending to minus infinity without boundedness. -/
theorem layer_tail_positive_of_positive_deficit {B c : ℝ}
    (hy2 : y<2) (hB : Tendsto (fun a=>max (F.layerDeficit a) 0) l (𝓝 B))
    (hc : y*B^2<(θ-3*c)*(2-y)) :
    ∀ᶠ a in l,∀ ξ∈Icc (0:ℝ) 2,
      0<scaledTail (F.epsilon a) c (F.thetaAt a) (F.tuning a).stepSize
        (F.tuning a).tau ξ := by
  have hd : 0<2*(2-y) := by linarith
  have hlim : (-4*y*B)^2<4*((2*y*(θ-3*c))*(2*(2-y))) := by
    convert mul_lt_mul_of_pos_left hc (mul_pos (show (0:ℝ)<16 by norm_num) F.step_pos) using 1 <;> ring
  have hp3 : Tendsto (fun a=>scaledP3 (F.epsilon a) c (F.thetaAt a)
      (F.tuning a).stepSize (F.tuning a).tau) l (𝓝 (2*(2-y))) := by
    have hv : 4*(1-(1/2)*y)=2*(2-y) := by ring
    simpa only [hv] using F.P3_tendsto c
  have hdisc := ((F.layerLowerMiddle_tendsto c hB).pow 2).eventually_lt
    (((F.P1_div_tendsto c).mul hp3).const_mul 4) hlim
  filter_upwards [F.epsilon_pos,F.layerLowerMiddle_le c,
    hp3.eventually (eventually_gt_nhds hd),hdisc] with a he hb hd hdisc ξ hξ
  exact tail_pos_of_rescaled (Real.sq_sqrt he.le) (Real.sqrt_pos.mpr he) hd
    (by simpa only [mul_assoc] using hdisc) hb hξ.1

theorem layer_lagOne_upper {B c : ℝ} (hy2 : y<2)
    (hB : Tendsto F.layerDeficit l (𝓝 B)) (hc0 : 0<c) (hc : c<Layer.constant θ y B) :
    ∀ᶠ a in l,Momentum.momentumRate (F.tuning a).beta (F.tuning a).tau
      (F.tuning a).stepSize (F.tuning a).step_pos.ne' (F.epsilon a^2) 1<1-c*F.epsilon a := by
  have hcq : c<Flow.cQ θ y := hc.trans_le (min_le_left _ _)
  have hcl : 3*c<Layer.Lambda θ y B := by
    have hh := hc.trans_le (min_le_right _ _)
    linarith
  have hdisc : y*(max B 0)^2<(θ-3*c)*(2-y) := by
    have hh : y*(max B 0)^2/(2-y)<θ-3*c := by
      unfold Layer.Lambda at hcl
      linarith
    exact (div_lt_iff₀ (by linarith : 0<2-y)).mp hh
  exact (F.lag_scaled hc0 hcq
    (F.layer_tail_positive_of_positive_deficit hy2 (F.positive_deficit_tendsto hB) hdisc)).mono
      fun _ h=>h.2.2

theorem layer_lagOne_upper_atBot {c : ℝ} (hy2 : y<2)
    (hB : Tendsto F.layerDeficit l atBot) (hc0 : 0<c) (hc : c<Flow.cF θ y) :
    ∀ᶠ a in l,Momentum.momentumRate (F.tuning a).beta (F.tuning a).tau
      (F.tuning a).stepSize (F.tuning a).step_pos.ne' (F.epsilon a^2) 1<1-c*F.epsilon a := by
  have hcq : c<Flow.cQ θ y := hc.trans_le (min_le_right _ _)
  have hct : c<θ/3 := hc.trans_le (min_le_left _ _)
  have hdisc : y*(0:ℝ)^2<(θ-3*c)*(2-y) := by
    simpa only [zero_pow (by omega : 2≠0),mul_zero] using
      mul_pos (show 0<θ-3*c by linarith) (show 0<2-y by linarith)
  exact (F.lag_scaled hc0 hcq
    (F.layer_tail_positive_of_positive_deficit hy2
      (F.positive_deficit_tendsto_of_atBot hB) hdisc)).mono fun _ h=>h.2.2

/-- The source quantifies over every real c below the layer constant. -/
theorem layer_upper {B c : ℝ} (hy2 : y<2)
    (hB : Tendsto F.layerDeficit l (𝓝 B)) (hBA : B<Layer.Astar θ y)
    (hc : c<Layer.constant θ y B) :
    ∀ᶠ a in l,Momentum.momentumRate (F.tuning a).beta (F.tuning a).tau
      (F.tuning a).stepSize (F.tuning a).step_pos.ne' (F.epsilon a^2) 1<1-c*F.epsilon a := by
  have hp := (Layer.constant_pos_iff F.theta_pos F.step_pos hy2).mpr hBA
  obtain ⟨d,hd,hdup⟩ := exists_between (max_lt hc hp)
  have hd0 : 0<d := (le_max_right c 0).trans_lt hd
  have hcd : c<d := (le_max_left c 0).trans_lt hd
  filter_upwards [F.layer_lagOne_upper hy2 hB hd0 hdup,F.epsilon_pos] with a ha he
  exact ha.trans (by nlinarith [mul_pos (sub_pos.mpr hcd) he])

theorem layer_upper_atBot {c : ℝ} (hy2 : y<2)
    (hB : Tendsto F.layerDeficit l atBot) (hc : c<Flow.cF θ y) :
    ∀ᶠ a in l,Momentum.momentumRate (F.tuning a).beta (F.tuning a).tau
      (F.tuning a).stepSize (F.tuning a).step_pos.ne' (F.epsilon a^2) 1<1-c*F.epsilon a := by
  have hp := Flow.cF_pos F.theta_pos F.step_pos
  obtain ⟨d,hd,hdup⟩ := exists_between (max_lt hc hp)
  have hd0 : 0<d := (le_max_right c 0).trans_lt hd
  have hcd : c<d := (le_max_left c 0).trans_lt hd
  filter_upwards [F.layer_lagOne_upper_atBot hy2 hB hd0 hdup,F.epsilon_pos] with a ha he
  exact ha.trans (by nlinarith [mul_pos (sub_pos.mpr hcd) he])

theorem layer_tail_positive_of_deficit_le {B c : ℝ} (hy2 : y<2)
    (hB : ∀ᶠ a in l,F.layerDeficit a≤B)
    (hc : y*(max B 0)^2<(θ-3*c)*(2-y)) :
    ∀ᶠ a in l,∀ ξ∈Icc (0:ℝ) 2,
      0<scaledTail (F.epsilon a) c (F.thetaAt a) (F.tuning a).stepSize
        (F.tuning a).tau ξ := by
  let L : A→ℝ := fun a=> -4*(F.tuning a).stepSize*max B 0-
    |Real.sqrt (F.epsilon a)*F.layerError c 1 a|
  have hL : Tendsto L l (𝓝 (-4*y*max B 0)) := by
    have ht := ((F.step_tendsto.const_mul (-4)).mul_const (max B 0)).sub
      ((F.sqrt_epsilon_tendsto.mul (F.layerError_tendsto c 1)).abs)
    simpa only [zero_mul,abs_zero,sub_zero] using ht
  have hLower : ∀ᶠ a in l,L a≤scaledP2 (F.epsilon a) c (F.thetaAt a)
      (F.tuning a).stepSize (F.tuning a).tau/Real.sqrt (F.epsilon a) := by
    filter_upwards [hB,F.P2_layer_exact c] with a hB hP2
    rw [hP2]
    have hm := mul_le_mul_of_nonneg_left (hB.trans (le_max_left B 0))
      (mul_nonneg (show (0:ℝ)≤4 by norm_num) (F.tuning a).step_pos.le)
    have hab := neg_abs_le (Real.sqrt (F.epsilon a)*F.layerError c 1 a)
    dsimp [L]
    linarith
  have hd : 0<2*(2-y) := by linarith
  have hlim : (-4*y*max B 0)^2<4*((2*y*(θ-3*c))*(2*(2-y))) := by
    convert mul_lt_mul_of_pos_left hc (mul_pos (show (0:ℝ)<16 by norm_num) F.step_pos) using 1 <;> ring
  have hp3 : Tendsto (fun a=>scaledP3 (F.epsilon a) c (F.thetaAt a)
      (F.tuning a).stepSize (F.tuning a).tau) l (𝓝 (2*(2-y))) := by
    have hv : 4*(1-(1/2)*y)=2*(2-y) := by ring
    simpa only [hv] using F.P3_tendsto c
  have hdisc := (hL.pow 2).eventually_lt (((F.P1_div_tendsto c).mul hp3).const_mul 4) hlim
  filter_upwards [F.epsilon_pos,hLower,hp3.eventually (eventually_gt_nhds hd),hdisc]
    with a he hb hd hdisc ξ hξ
  exact tail_pos_of_rescaled (Real.sq_sqrt he.le) (Real.sqrt_pos.mpr he) hd
    (by simpa only [mul_assoc] using hdisc) hb hξ.1

/-- A uniform upper bound on the layer coordinate gives the upper certificate
without assuming that the actual deficit converges. -/
theorem layer_upper_of_deficit_le {B c : ℝ} (hy2 : y<2)
    (hB : ∀ᶠ a in l,F.layerDeficit a≤B) (hBA : B<Layer.Astar θ y)
    (hc : c<Layer.constant θ y B) :
    ∀ᶠ a in l,Momentum.momentumRate (F.tuning a).beta (F.tuning a).tau
      (F.tuning a).stepSize (F.tuning a).step_pos.ne' (F.epsilon a^2) 1<1-c*F.epsilon a := by
  have hp := (Layer.constant_pos_iff F.theta_pos F.step_pos hy2).mpr hBA
  obtain ⟨d,hd,hdup⟩ := exists_between (max_lt hc hp)
  have hd0 : 0<d := (le_max_right c 0).trans_lt hd
  have hcd : c<d := (le_max_left c 0).trans_lt hd
  have hdq : d<Flow.cQ θ y := hdup.trans_le (min_le_left _ _)
  have hdl : 3*d<Layer.Lambda θ y B := by
    have hh := hdup.trans_le (min_le_right _ _)
    linarith
  have hdisc : y*(max B 0)^2<(θ-3*d)*(2-y) := by
    have hh : y*(max B 0)^2/(2-y)<θ-3*d := by
      unfold Layer.Lambda at hdl
      linarith
    exact (div_lt_iff₀ (by linarith : 0<2-y)).mp hh
  have hu := (F.lag_scaled hd0 hdq (F.layer_tail_positive_of_deficit_le hy2 hB hdisc)).mono
    fun _ h=>h.2.2
  filter_upwards [hu,F.epsilon_pos] with a ha he
  exact ha.trans (by nlinarith [mul_pos (sub_pos.mpr hcd) he])

end
end nesterov.TwoStep.Scaling
