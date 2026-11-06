import nesterov.FiniteCondition.Thresholds

/-! The unnumbered finite-condition conclusions following tonguefree. -/
namespace nesterov.FiniteCondition
noncomputable section
open TwoStep Set Filter
open scoped Topology

/-- Above the three-cycle threshold the low and intermediate frequencies
already have a positive lag-one polynomial. -/
theorem lagOne_pos_up_to_three_halves {β τ yμ y ξ : ℝ}
    (hβ : 0≤β) (hβ1 : β<1) (hτ : 0≤τ) (ht : tauThree β≤τ)
    (hμ : 0<yμ) (hy : yμ<y) (hym : y<maxStep β τ)
    (hξ : ξ∈Ioc (0:ℝ) (3/2)) : 0<Ltau β τ yμ y ξ := by
  have hm := maxStep_pos hβ hτ
  have hb0 : 0≤1-β^2 := by nlinarith
  have hb3 : 0≤boundaryFactor β τ (3/2) := by
    rw [boundaryFactor_three_halves]
    positivity
  have hb : 0≤boundaryFactor β τ ξ := by
    have he : boundaryFactor β τ ξ=
        (1-2*ξ/3)*(1-β^2)+(2*ξ/3)*boundaryFactor β τ (3/2) := by
      unfold boundaryFactor
      ring
    rw [he]
    exact add_nonneg (mul_nonneg (by linarith [hξ.2]) hb0)
      (mul_nonneg (by positivity [hξ.1]) hb3)
  have hmax : 0≤Ltau β τ 0 (maxStep β τ) ξ := by
    rw [Ltau_maxStep (by positivity : 1+2*τ≠0)]
    exact mul_nonneg (div_nonneg (by linarith [hξ.2]) (by positivity)) hb
  have hy0 := hμ.trans hy
  have hzero : 0<Ltau β τ 0 y ξ := by
    have ht0 : 0≤y/maxStep β τ := div_nonneg hy0.le hm.le
    have ht1 : y/maxStep β τ<1 := (div_lt_one hm).mpr hym
    have hh : 0<(1-y/maxStep β τ)*Ltau β τ 0 0 ξ+
        (y/maxStep β τ)*Ltau β τ 0 (maxStep β τ) ξ :=
      add_pos_of_pos_of_nonneg
        (mul_pos (sub_pos.mpr ht1) (zero_step_pos (τ:=τ) hβ hβ1 hξ.1))
        (mul_nonneg ht0 hmax)
    rw [←Ltau_affine_step] at hh
    simpa only [mul_zero,zero_add,div_mul_cancel₀ _ hm.ne'] using hh
  rw [Ltau_interpolate hy0.ne']
  exact add_pos_of_pos_of_nonneg
    (mul_pos (sub_pos.mpr ((div_lt_one hy0).mpr hy)) hzero)
    (mul_nonneg (div_nonneg hμ.le hy0.le)
      (diagonal_pos_of_nonzero ⟨hξ.1.le,by linarith [hξ.2]⟩
        (diagonal_nonzero_of_margin hβ hβ1 hτ hy0 hym)).le)

theorem stable_lagOne_pos_up_to_three_halves (q : Momentum.Tuning) {μ L ξ : ℝ}
    (hμ : 0<μ) (hμL : μ<L) (hs : q.Stable μ L) (ht : tauThree q.beta≤q.tau)
    (hξ : ξ∈Ioc (0:ℝ) (3/2)) :
    0<Ltau q.beta q.tau (q.stepSize*μ) (q.stepSize*L) ξ := by
  exact lagOne_pos_up_to_three_halves q.beta_nonneg q.beta_lt_one q.tau_nonneg ht
    (mul_pos q.step_pos hμ) (mul_lt_mul_of_pos_left hμL q.step_pos)
    ((lt_div_iff₀ (by linarith [q.tau_nonneg] : 0<1+2*q.tau)).mpr
      ((q.stable_iff hμ hμL).mp hs)) hξ

/-- In the gap between the two thresholds a negative lag-one symbol can occur
only on the literal source open frequency interval (2π/3,π). -/
theorem negative_lagOne_frequency (q : Momentum.Tuning) {μ L ω : ℝ}
    (hμ : 0<μ) (hμL : μ<L) (hs : q.Stable μ L) (ht : tauThree q.beta≤q.tau)
    (hω : ω∈Ioc (0:ℝ) Real.pi)
    (hneg : Ltau q.beta q.tau (q.stepSize*μ) (q.stepSize*L) (1-Real.cos ω)<0) :
    ω∈Ioo (2*Real.pi/3) Real.pi := by
  have hcos : Real.cos (2*Real.pi/3)= -(1:ℝ)/2 := by
    rw [show 2*Real.pi/3=2*(Real.pi/3) by ring,Real.cos_two_mul,Real.cos_pi_div_three]
    norm_num
  have hξ : 0<1-Real.cos ω := sub_pos.mpr (by
    simpa only [Real.cos_zero] using Real.cos_lt_cos_of_nonneg_of_le_pi
      (by norm_num : (0:ℝ)≤0) hω.2 hω.1)
  constructor
  · by_contra hn
    have hc := Real.cos_le_cos_of_nonneg_of_le_pi hω.1.le
      (by linarith [Real.pi_pos] : 2*Real.pi/3≤Real.pi) (le_of_not_gt hn)
    rw [hcos] at hc
    have hp := stable_lagOne_pos_up_to_three_halves q hμ hμL hs ht
      (ξ:=1-Real.cos ω) ⟨hξ,by linarith⟩
    linarith
  · apply lt_of_le_of_ne hω.2
    intro he
    have hh := stable_Ltau_two_pos q hμ hμL hs
    rw [he,Real.cos_pi] at hneg
    norm_num at hneg
    linarith

/-- The nonempty heavy-ball gap has convergence for every stable tuning,
while a strict failure of the lag-one criterion exists. -/
theorem heavyBall_lagTwo_gap {β : ℝ} (hβ : 0≤β) (hβ1 : β<1)
    (hlo : Real.sqrt 5-2<β) (hhi : β≤(Real.sqrt 13-3)/2) :
    AllStableTuningsConverge β 0 ∧ ∃ μ L ξ : ℝ,0<μ ∧ μ<L ∧
      Quadratic.Stable μ L β 0 1 ∧ ξ∈Ioo (0:ℝ) 2 ∧ Ltau β 0 μ L ξ<0 := by
  refine ⟨(heavyBall_all_stable_iff hβ hβ1).mpr hhi,?_⟩
  have hs : 0<tauStar β := lt_of_not_ge (fun h=>
    (not_le_of_gt hlo) ((heavyBall_lagOne_threshold hβ).mp h))
  exact lagOne_negative hβ hβ1 le_rfl hs

/-- Both finite-condition thresholds tend to the half-step wall. -/
theorem thresholds_tendsto_wall {A : Type*} {l : Filter A} {β : A→ℝ}
    (hβ : Tendsto β l (𝓝 1)) :
    Tendsto (fun a=>tauThree (β a)) l (𝓝 (1/2)) ∧
      Tendsto (fun a=>tauStar (β a)) l (𝓝 (1/2)) := by
  have hc3 : Continuous tauThree := by unfold tauThree;fun_prop
  have hcs : Continuous tauStar := by unfold tauStar;fun_prop
  have h3 : tauThree 1=(1/2:ℝ) := by norm_num [tauThree]
  have hs : tauStar 1=(1/2:ℝ) := by norm_num [tauStar]
  exact ⟨by simpa only [Function.comp_def,h3] using (hc3.tendsto 1).comp hβ,
    by simpa only [Function.comp_def,hs] using (hcs.tendsto 1).comp hβ⟩

end
end nesterov.FiniteCondition
