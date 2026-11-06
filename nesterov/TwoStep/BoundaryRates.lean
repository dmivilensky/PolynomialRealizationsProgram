import nesterov.TwoStep.BoundaryUpper
import nesterov.TwoStep.Lower

/-! Article: Proposition `prop:boundary`, both actual nonlinear distance factors.
The full-class and initialized-from-rest limits are matched by the literal
lag-one upper bound, sampled flow spectra, and the largest-curvature quadratic. -/
namespace nesterov.TwoStep.Scaling
noncomputable section
open Filter Set
open scoped Topology
variable {θ y τ : ℝ} (F : Scaling ℝ (𝓝[>] (0:ℝ)) θ y τ)

private theorem full_le_rest_coefficient :
    ∀ᶠ ε in 𝓝[>] (0:ℝ),F.fullCoefficient ε≤F.restCoefficient ε := by
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds (by norm_num : (0:ℝ)<1)).filter_mono nhdsWithin_le_nhds]
    with ε he he1
  have hp : 0<ε := he
  exact div_le_div_of_nonneg_right (sub_le_sub_left
    (Momentum.restRate_le_momentumRate (β:=(F.tuning ε).beta) (τ:=(F.tuning ε).tau)
      (F.tuning ε).step_pos.ne' (sq_pos_of_pos hp) (by nlinarith : ε^2<1)) 1) hp.le

private theorem coefficients_tendsto_of_bounds (he : F.epsilon=id) {m : ℝ} (hm : 0<m)
    (hupper : ∀ c : ℝ,0<c → c<m → ∀ᶠ a in 𝓝[>] (0:ℝ),
      Momentum.momentumRate (F.tuning a).beta (F.tuning a).tau (F.tuning a).stepSize
        (F.tuning a).step_pos.ne' (F.epsilon a^2) 1<1-c*F.epsilon a)
    (hceiling : ∀ b : ℝ,m<b → ∀ᶠ ε in 𝓝[>] (0:ℝ),F.restCoefficient ε<b) :
    Tendsto F.fullCoefficient (𝓝[>] (0:ℝ)) (𝓝 m) ∧
      Tendsto F.restCoefficient (𝓝[>] (0:ℝ)) (𝓝 m) := by
  have hlo (c : ℝ) (hc : c<m) :
      ∀ᶠ ε in 𝓝[>] (0:ℝ),c<F.fullCoefficient ε ∧ c<F.restCoefficient ε := by
    obtain ⟨d,hcd,hdm⟩ := exists_between (max_lt hc hm)
    have hd0 : 0<d := (le_max_right c 0).trans_lt hcd
    have hdc : c<d := (le_max_left c 0).trans_lt hcd
    have hu := hupper d hd0 hdm
    rw [he] at hu
    filter_upwards [hu,F.full_le_rest_coefficient,self_mem_nhdsWithin] with ε hu hcomp hε
    have hep : 0<ε := hε
    simp only [id_eq] at hu
    have hf : d<F.fullCoefficient ε := by
      apply (lt_div_iff₀ hep).mpr
      change d*ε<1-Momentum.momentumRate (F.tuning ε).beta (F.tuning ε).tau
        (F.tuning ε).stepSize (F.tuning ε).step_pos.ne' (ε^2) 1
      simpa only [id_eq] using (show d*ε<1-Momentum.momentumRate (F.tuning ε).beta
        (F.tuning ε).tau (F.tuning ε).stepSize (F.tuning ε).step_pos.ne' (ε^2) 1 by linarith)
    exact ⟨hdc.trans hf,(hdc.trans hf).trans_le hcomp⟩
  constructor
  · apply tendsto_order.mpr
    exact ⟨fun c hc=>(hlo c hc).mono fun _ ha=>ha.1,
      fun b hb=>((hceiling b hb).and F.full_le_rest_coefficient).mono fun _ ha=>ha.2.trans_lt ha.1⟩
  · apply tendsto_order.mpr
    exact ⟨fun c hc=>(hlo c hc).mono fun _ ha=>ha.2,hceiling⟩

/-- Proposition boundary, finite scaled stability margin. -/
theorem boundary_coefficients_tendsto (he : F.epsilon=id)
    (hstable : ∀ᶠ ε in 𝓝[>] (0:ℝ),(F.tuning ε).Stable (ε^2) 1)
    {s : ℝ} (hτ : 1/2<τ) (hboundary : y*(1+2*τ)=4)
    (hs : Tendsto F.stabilityMargin (𝓝[>] (0:ℝ)) (𝓝 s)) (hsθ : 2*θ<s) :
    Tendsto F.fullCoefficient (𝓝[>] (0:ℝ)) (𝓝 (min (Flow.cF θ y) (alternatingConstant θ τ s))) ∧
      Tendsto F.restCoefficient (𝓝[>] (0:ℝ)) (𝓝 (min (Flow.cF θ y) (alternatingConstant θ τ s))) := by
  have hcp : 0<alternatingConstant θ τ s := by
    unfold alternatingConstant
    exact div_pos (mul_pos (sub_pos.mpr hsθ) (by linarith)) (by linarith)
  apply F.coefficients_tendsto_of_bounds he (lt_min (Flow.cF_pos F.theta_pos F.step_pos) hcp)
  · intro c hc0 hc
    exact F.boundary_lagOne_upper hc0 (hc.trans_le (min_le_left _ _)) hτ hboundary hs
      (hc.trans_le (min_le_right _ _))
  · intro b hb
    rcases le_total (Flow.cF θ y) (alternatingConstant θ τ s) with hF|hpi
    · rw [min_eq_left hF] at hb
      obtain ⟨d,hd,hdb⟩ := exists_between hb
      exact (F.rest_coefficient_eventually_le he hstable hd).mono fun _ ha=>ha.trans_lt hdb
    · rw [min_eq_right hpi] at hb
      have hstable' : ∀ᶠ a in 𝓝[>] (0:ℝ),(F.tuning a).Stable (F.epsilon a^2) 1 := by
        simpa only [he,id_eq] using hstable
      have hshift := (F.alternating_shift_scaled_tendsto hτ.le hboundary hstable' hs).eventually
        (eventually_lt_nhds hb)
      have hmode := F.alternating_rate_lower hτ.le hboundary hstable'
      rw [he] at hshift hmode
      filter_upwards [hshift,hmode,self_mem_nhdsWithin] with ε hshift hmode hε
      simp only [id_eq] at hmode hshift
      have hbound : F.restCoefficient ε≤alternatingShift (F.tuning ε)/ε :=
        div_le_div_of_nonneg_right (by linarith only [hmode.2.1]) hε.le
      exact hbound.trans_lt (by simpa only [id_eq] using hshift)

/-- Proposition boundary when the scaled stability margin tends to infinity. -/
theorem boundary_coefficients_tendsto_infinite (he : F.epsilon=id)
    (hstable : ∀ᶠ ε in 𝓝[>] (0:ℝ),(F.tuning ε).Stable (ε^2) 1)
    (hτ : 1/2<τ) (hboundary : y*(1+2*τ)=4)
    (hs : Tendsto F.stabilityMargin (𝓝[>] (0:ℝ)) atTop) :
    Tendsto F.fullCoefficient (𝓝[>] (0:ℝ)) (𝓝 (Flow.cF θ y)) ∧
      Tendsto F.restCoefficient (𝓝[>] (0:ℝ)) (𝓝 (Flow.cF θ y)) := by
  apply F.coefficients_tendsto_of_bounds he (Flow.cF_pos F.theta_pos F.step_pos)
  · exact fun c hc0 hc=>F.boundary_lagOne_upper_infinite hc0 hc hτ hboundary hs
  · intro b hb
    obtain ⟨d,hd,hdb⟩ := exists_between hb
    exact (F.rest_coefficient_eventually_le he hstable hd).mono fun _ ha=>ha.trans_lt hdb

end
end nesterov.TwoStep.Scaling
