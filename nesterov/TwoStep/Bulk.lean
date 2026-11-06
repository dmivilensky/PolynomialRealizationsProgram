import nesterov.TwoStep.Lower
import nesterov.TwoStep.LagScaled

/-! Article: Theorem B(b,c), the exact full-class and from-rest bulk constant. -/
namespace nesterov.TwoStep.Scaling
noncomputable section
open Filter Set Flow
open scoped Topology
variable {θ y τ : ℝ} (F : Scaling ℝ (𝓝[>] (0:ℝ)) θ y τ)

 theorem bulk_coefficients_tendsto (he : F.epsilon=id)
    (hs : ∀ᶠ ε in 𝓝[>] (0:ℝ),(F.tuning ε).Stable (ε^2) 1)
    (hτ : 1/2<τ) (hmargin : y*(1+2*τ)<4) :
    Tendsto F.fullCoefficient (𝓝[>] (0:ℝ)) (𝓝 (cF θ y)) ∧
      Tendsto F.restCoefficient (𝓝[>] (0:ℝ)) (𝓝 (cF θ y)) := by
  have hcf : 0<cF θ y := cF_pos F.theta_pos F.step_pos
  have hbelow (a : ℝ) (ha : a<cF θ y) :
      ∀ᶠ ε in 𝓝[>] (0:ℝ),a<F.fullCoefficient ε ∧ a<F.restCoefficient ε := by
    obtain ⟨c,hc,hccf⟩ := exists_between (max_lt (by exact hcf) ha)
    have hc0 : 0<c := (le_max_left 0 a).trans_lt hc
    have hac : a<c := (le_max_right 0 a).trans_lt hc
    have hh := F.bulk_lagOne_upper hc0 hccf hτ hmargin
    rw [he] at hh
    filter_upwards [hh,self_mem_nhdsWithin,
      (eventually_lt_nhds zero_lt_one).filter_mono nhdsWithin_le_nhds] with ε hε heps hε1
    have hp : 0<ε := heps
    have hrate : Momentum.momentumRate (F.tuning ε).beta (F.tuning ε).tau (F.tuning ε).stepSize
        (F.tuning ε).step_pos.ne' (ε^2) 1<1-c*ε := by simpa only [id_eq] using hε
    have hfull : c<F.fullCoefficient ε :=
      (lt_div_iff₀ hp).mpr (by change c*ε<1-_;linarith)
    have hrest := Momentum.restRate_le_momentumRate (β:=(F.tuning ε).beta) (τ:=(F.tuning ε).tau) (F.tuning ε).step_pos.ne'
      (sq_pos_of_pos hp) (by nlinarith : ε^2<1)
    have hm : F.fullCoefficient ε≤F.restCoefficient ε :=
      div_le_div_of_nonneg_right (sub_le_sub_left hrest 1) hp.le
    exact ⟨hac.trans hfull,hac.trans (hfull.trans_le hm)⟩
  have habove (a : ℝ) (ha : cF θ y<a) :
      ∀ᶠ ε in 𝓝[>] (0:ℝ),F.fullCoefficient ε<a ∧ F.restCoefficient ε<a := by
    obtain ⟨b,hb,hba⟩ := exists_between ha
    filter_upwards [F.rest_coefficient_eventually_le he hs hb,self_mem_nhdsWithin,
      (eventually_lt_nhds zero_lt_one).filter_mono nhdsWithin_le_nhds] with ε hε heps hε1
    have hp : 0<ε := heps
    have hrest := Momentum.restRate_le_momentumRate (β:=(F.tuning ε).beta) (τ:=(F.tuning ε).tau) (F.tuning ε).step_pos.ne'
      (sq_pos_of_pos hp) (by nlinarith : ε^2<1)
    have hm : F.fullCoefficient ε≤F.restCoefficient ε :=
      div_le_div_of_nonneg_right (sub_le_sub_left hrest 1) hp.le
    exact ⟨(hm.trans hε).trans_lt hba,hε.trans_lt hba⟩
  constructor <;> apply tendsto_order.mpr
  · exact ⟨fun a ha=>(hbelow a ha).mono fun _ h=>h.1,
      fun a ha=>(habove a ha).mono fun _ h=>h.1⟩
  · exact ⟨fun a ha=>(hbelow a ha).mono fun _ h=>h.2,
      fun a ha=>(habove a ha).mono fun _ h=>h.2⟩

end
end nesterov.TwoStep.Scaling
