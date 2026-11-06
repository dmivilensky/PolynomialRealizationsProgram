import nesterov.TwoStep.KnownQHMRates

/-! Corollary B(iii-b): the actual initialized QHM rate in the strict bulk. -/
namespace nesterov.TwoStep.KnownTunings
noncomputable section
open Filter Set
open scoped Topology

theorem qhm_bulk_rate {α β ν : ℝ→ℝ} {θ y τ : ℝ}
    (hθ : 0<θ) (hy : 0<y) (hτ : 1/2<τ) (hmargin : y*(1+2*τ)<4)
    (hbeta : Tendsto (fun ε : ℝ=>(1-β ε)/ε) (𝓝[>] (0:ℝ)) (𝓝 θ))
    (hstep : Tendsto (fun ε : ℝ=>α ε*(1-β ε)) (𝓝[>] (0:ℝ)) (𝓝 y))
    (htau : Tendsto (fun ε : ℝ=>Momentum.qhmExtrapolation (β ε) (ν ε)) (𝓝[>] (0:ℝ)) (𝓝 τ)) :
    Tendsto (fun ε : ℝ=>(1-Momentum.qhmRate (α ε) (β ε) (ν ε) (ε^2) 1)/ε)
      (𝓝[>] (0:ℝ)) (𝓝 (Flow.cF θ y)) := by
  let F := fromRawLimits β (fun ε=>Momentum.qhmExtrapolation (β ε) (ν ε))
    (fun ε=>α ε*(1-β ε)) hθ hy (show 0<τ by linarith) hbeta hstep htau
  have hparams : ∀ᶠ ε in 𝓝[>] (0:ℝ),(F.tuning ε).beta=β ε ∧
      (F.tuning ε).tau=Momentum.qhmExtrapolation (β ε) (ν ε) ∧
      (F.tuning ε).stepSize=α ε*(1-β ε) :=
    fromRawLimits_parameters _ _ _ hθ hy (show 0<τ by linarith) hbeta hstep htau
  have he : Tendsto (fun ε : ℝ=>ε) (𝓝[>] (0:ℝ)) (𝓝 0) := continuous_id.continuousWithinAt.tendsto
  have hstable : ∀ᶠ ε in 𝓝[>] (0:ℝ),(F.tuning ε).Stable (ε^2) 1 := by
    filter_upwards [F.bulk_rate_eventually_lt (Flow.cQ_pos hθ hy) hmargin,self_mem_nhdsWithin,
      he.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1))] with ε hr he0 he1
    have hep : 0<ε := he0
    apply (Quadratic.stable_iff_quadraticRate_lt_one (by nlinarith : ε^2≤1)).mpr
    simpa only [Scaling.rate,F,fromRawLimits,zero_mul,sub_zero,id_eq] using hr
  have hc := (F.bulk_coefficients_tendsto rfl hstable hτ hmargin).2
  have hrest : Tendsto (fun ε : ℝ=>Momentum.momentumRestRate (F.tuning ε).beta (F.tuning ε).tau
      (F.tuning ε).stepSize (F.tuning ε).step_pos.ne' (ε^2) 1) (𝓝[>] (0:ℝ)) (𝓝 1) := by
    have ht := (tendsto_const_nhds (x:=(1:ℝ))).sub (he.mul hc)
    simp only [zero_mul,sub_zero] at ht
    apply ht.congr'
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hep : 0<ε := hε
    unfold Scaling.restCoefficient
    field_simp [hep.ne']
    ring
  have htaubound : ∀ᶠ ε in 𝓝[>] (0:ℝ),0≤(F.tuning ε).tau ∧ (F.tuning ε).tau≤τ+1 := by
    filter_upwards [F.tau_tendsto.eventually (eventually_lt_nhds (show τ<τ+1 by linarith))] with ε hε
    exact ⟨(F.tuning ε).tau_nonneg,hε.le⟩
  have hquery := Momentum.eventually_queryRate_eq_of_rest_tendsto_one
    (fun ε=>(F.tuning ε).beta) (fun ε=>(F.tuning ε).tau) (fun ε=>(F.tuning ε).stepSize)
    (fun ε : ℝ=>ε^2) (fun _=>1) (fun ε=>(F.tuning ε).step_pos.ne')
    (B:=τ+1) (by linarith) htaubound hrest
  have heq : ∀ᶠ ε in 𝓝[>] (0:ℝ),Momentum.qhmRate (α ε) (β ε) (ν ε) (ε^2) 1=
      Momentum.momentumRestRate (F.tuning ε).beta (F.tuning ε).tau
        (F.tuning ε).stepSize (F.tuning ε).step_pos.ne' (ε^2) 1 := by
    filter_upwards [hparams,hquery] with ε hp hq
    have hβ : β ε≠1 := by rw [←hp.1];exact (F.tuning ε).beta_lt_one.ne
    have hh : α ε*(1-β ε)≠0 := by rw [←hp.2.2];exact (F.tuning ε).step_pos.ne'
    have hd := Momentum.qhmRate_eq_queryRestRate (α ε) (β ε) (ν ε) (ε^2) 1 hβ hh
    have hd' : Momentum.qhmRate (α ε) (β ε) (ν ε) (ε^2) 1=
        Momentum.queryRestRate (F.tuning ε).beta (F.tuning ε).tau (F.tuning ε).stepSize
          (F.tuning ε).step_pos.ne' (ε^2) 1 := by
      simpa only [hp.1,hp.2.1,hp.2.2] using hd
    exact hd'.trans hq
  apply hc.congr'
  filter_upwards [heq] with ε hε
  unfold Scaling.restCoefficient
  rw [hε]

end
end nesterov.TwoStep.KnownTunings
