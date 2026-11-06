import nesterov.TwoStep.AsymptoticsBridge

/-! Physical representatives of parameter germs, retaining exact eventual parameters. -/
namespace nesterov.TwoStep
noncomputable section
open Filter Set
open scoped Topology

def physicalTuning (β τ h : ℝ) : Momentum.Tuning :=
  if H : 0≤β ∧ β<1 ∧ 0≤τ ∧ 0<h then
    { beta := β
      tau := τ
      stepSize := h
      beta_nonneg := H.1
      beta_lt_one := H.2.1
      tau_nonneg := H.2.2.1
      step_pos := H.2.2.2 }
  else
    { beta := 0
      tau := 0
      stepSize := 1
      beta_nonneg := le_rfl
      beta_lt_one := by norm_num
      tau_nonneg := le_rfl
      step_pos := by norm_num }

theorem physicalTuning_parameters {β τ h : ℝ} (H : 0≤β ∧ β<1 ∧ 0≤τ ∧ 0<h) :
    (physicalTuning β τ h).beta=β ∧ (physicalTuning β τ h).tau=τ ∧
      (physicalTuning β τ h).stepSize=h := by
  simp [physicalTuning,H]

theorem raw_physical_eventually {β t h : ℝ→ℝ} {θ y τ : ℝ}
    (hθ : 0<θ) (hy : 0<y) (hτ : 0<τ)
    (hbeta : Tendsto (fun ε=>(1-β ε)/ε) (𝓝[>] (0:ℝ)) (𝓝 θ))
    (hstep : Tendsto h (𝓝[>] (0:ℝ)) (𝓝 y))
    (htau : Tendsto t (𝓝[>] (0:ℝ)) (𝓝 τ)) :
    ∀ᶠ ε in 𝓝[>] (0:ℝ),0≤β ε ∧ β ε<1 ∧ 0≤t ε ∧ 0<h ε := by
  have he : Tendsto (fun ε : ℝ=>ε) (𝓝[>] (0:ℝ)) (𝓝 0) :=
    continuous_id.continuousWithinAt.tendsto
  have hb : Tendsto β (𝓝[>] (0:ℝ)) (𝓝 1) := by
    have hh := (tendsto_const_nhds (x:=(1:ℝ))).sub (hbeta.mul he)
    simp only [mul_zero,sub_zero] at hh
    apply hh.congr'
    filter_upwards [self_mem_nhdsWithin] with ε hε
    change 0<ε at hε
    field_simp
    ring
  filter_upwards [self_mem_nhdsWithin,hb.eventually (eventually_gt_nhds (by norm_num : (0:ℝ)<1)),
    hbeta.eventually (eventually_gt_nhds hθ),hstep.eventually (eventually_gt_nhds hy),
    htau.eventually (eventually_gt_nhds hτ)] with ε hε hβ hslow hh ht
  change 0<ε at hε
  refine ⟨hβ.le,?_,ht.le,hh⟩
  have hp := (div_pos_iff.mp hslow).resolve_right (by rintro ⟨_,he⟩;linarith)
  linarith [hp.1]

def fromRawLimits (β t h : ℝ→ℝ) {θ y τ : ℝ} (hθ : 0<θ) (hy : 0<y) (hτ : 0<τ)
    (hbeta : Tendsto (fun ε=>(1-β ε)/ε) (𝓝[>] (0:ℝ)) (𝓝 θ))
    (hstep : Tendsto h (𝓝[>] (0:ℝ)) (𝓝 y))
    (htau : Tendsto t (𝓝[>] (0:ℝ)) (𝓝 τ)) :
    Scaling ℝ (𝓝[>] (0:ℝ)) θ y τ where
  epsilon := id
  tuning ε := physicalTuning (β ε) (t ε) (h ε)
  epsilon_tendsto := tendsto_id
  theta_tendsto := by
    apply hbeta.congr'
    filter_upwards [raw_physical_eventually hθ hy hτ hbeta hstep htau] with ε H
    rw [(physicalTuning_parameters H).1]
    rfl
  step_tendsto := by
    apply hstep.congr'
    filter_upwards [raw_physical_eventually hθ hy hτ hbeta hstep htau] with ε H
    exact (physicalTuning_parameters H).2.2.symm
  tau_tendsto := by
    apply htau.congr'
    filter_upwards [raw_physical_eventually hθ hy hτ hbeta hstep htau] with ε H
    exact (physicalTuning_parameters H).2.1.symm
  theta_pos := hθ
  step_pos := hy
  tau_nonneg := hτ.le

theorem fromRawLimits_parameters (β t h : ℝ→ℝ) {θ y τ : ℝ} (hθ : 0<θ) (hy : 0<y) (hτ : 0<τ)
    (hbeta : Tendsto (fun ε=>(1-β ε)/ε) (𝓝[>] (0:ℝ)) (𝓝 θ))
    (hstep : Tendsto h (𝓝[>] (0:ℝ)) (𝓝 y))
    (htau : Tendsto t (𝓝[>] (0:ℝ)) (𝓝 τ)) :
    ∀ᶠ ε in 𝓝[>] (0:ℝ),
      ((fromRawLimits β t h hθ hy hτ hbeta hstep htau).tuning ε).beta=β ε ∧
      ((fromRawLimits β t h hθ hy hτ hbeta hstep htau).tuning ε).tau=t ε ∧
      ((fromRawLimits β t h hθ hy hτ hbeta hstep htau).tuning ε).stepSize=h ε := by
  filter_upwards [raw_physical_eventually hθ hy hτ hbeta hstep htau] with ε H
  exact physicalTuning_parameters H

end
end nesterov.TwoStep
