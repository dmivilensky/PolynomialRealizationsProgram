import nesterov.TwoStep.FrontierRigidity

/-! Frontier(ii): acceleration on the full class limits the quadratic constant,
with no convergence assumption on the tuning parameters. -/
namespace nesterov.TwoStep
noncomputable section
open Filter Set
open scoped Topology

theorem full_acceleration_controls {A : Type*} {l : Filter A} {ε : A→ℝ} {q : A→Momentum.Tuning}
    {c : ℝ} (hc : 0<c) (he : Tendsto ε l (𝓝[>] (0:ℝ)))
    (hfull : ∀ᶠ a in l,Momentum.momentumRate (q a).beta (q a).tau (q a).stepSize
      (q a).step_pos.ne' (ε a^2) 1≤1-c*ε a) :
    ∀ᶠ a in l,(q a).Stable (ε a^2) 1 ∧
      Quadratic.quadraticRate (ε a^2) 1 (q a).beta (q a).tau (q a).stepSize≤1-c*ε a ∧
      Momentum.momentumRestRate (q a).beta (q a).tau (q a).stepSize (q a).step_pos.ne' (ε a^2) 1≤1 := by
  filter_upwards [hfull,he.eventually self_mem_nhdsWithin,
    (he.mono_right nhdsWithin_le_nhds).eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1))]
      with a hfull he he1
  have hμL : ε a^2<1 := by nlinarith
  have hq := (Momentum.quadraticRate_le_momentumRate (β:=(q a).beta) (τ:=(q a).tau)
    (q a).step_pos.ne' (sq_pos_of_pos he) hμL).trans hfull
  have hr := (Momentum.restRate_le_momentumRate (β:=(q a).beta) (τ:=(q a).tau)
    (q a).step_pos.ne' (sq_pos_of_pos he) hμL).trans hfull
  have hh : 1-c*ε a<1 := by nlinarith [mul_pos hc he]
  exact ⟨(Quadratic.stable_iff_quadraticRate_lt_one hμL.le).mpr (hq.trans_lt hh),hq,hr.trans hh.le⟩

theorem half_step_price_ceiling {τ : ℝ} (hτ : 1/2≤τ) :
    fixedExtrapolationCeiling τ≤Real.sqrt 2 := by
  have hp : 0<1+2*τ := by linarith
  unfold fixedExtrapolationCeiling
  apply (div_le_iff₀ (Real.sqrt_pos.mpr hp)).mpr
  have hm := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (show (2:ℝ)≤1+2*τ by linarith))
    (Real.sqrt_nonneg 2)
  nlinarith only [hm,Real.sq_sqrt (by norm_num : (0:ℝ)≤2)]

theorem accelerated_quadratic_eventually_lt {A : Type*} {l : Filter A} [NeBot l]
    [l.IsCountablyGenerated] {ε : A→ℝ} {q : A→Momentum.Tuning} {c a : ℝ}
    (hc : 0<c) (he : Tendsto ε l (𝓝[>] (0:ℝ)))
    (hfull : ∀ᶠ n in l,Momentum.momentumRate (q n).beta (q n).tau (q n).stepSize
      (q n).step_pos.ne' (ε n^2) 1≤1-c*ε n) (ha : Real.sqrt 2<a) :
    ∀ᶠ n in l,(1-Quadratic.quadraticRate (ε n^2) 1 (q n).beta (q n).tau (q n).stepSize)/ε n<a := by
  by_contra hh
  have hbad : ∃ᶠ n in l,a≤(1-Quadratic.quadraticRate (ε n^2) 1
      (q n).beta (q n).tau (q n).stepSize)/ε n := by
    simpa only [not_eventually,not_lt] using hh
  obtain ⟨s,hsl,hbad⟩ := exists_seq_forall_of_frequently hbad
  have heS := he.comp hsl
  have hcontrol := hsl.eventually (full_acceleration_controls hc he hfull)
  have hsS := hcontrol.mono fun _ h=>h.1
  have hqS := hcontrol.mono fun _ h=>h.2.1
  obtain ⟨φ,hφ,θ,y,τ,_,_,_,_,F,hFe,hFq⟩ := accelerated_subsequence hc heS hsS hqS
  have hsF : ∀ᶠ n in atTop,(F.tuning n).Stable (F.epsilon n^2) 1 := by
    simpa only [hFe,hFq,Function.comp_def] using hφ.tendsto_atTop.eventually hsS
  have hfullF : ∀ᶠ n in atTop,Momentum.momentumRate (F.tuning n).beta (F.tuning n).tau
      (F.tuning n).stepSize (F.tuning n).step_pos.ne' (F.epsilon n^2) 1≤1-c*F.epsilon n := by
    simpa only [hFe,hFq,Function.comp_def] using hφ.tendsto_atTop.eventually (hsl.eventually hfull)
  have hτ := F.half_le_tau_of_full_acceleration hc hsF hfullF
  have hceiling := fixed_tau_quadratic_eventually_lt F.epsilon_tendsto F.tau_tendsto
    ((half_step_price_ceiling hτ).trans_lt ha)
  obtain ⟨n,hn⟩ := hceiling.exists
  have hbadn := hbad (φ n)
  have hgood : (1-Quadratic.quadraticRate (ε (s (φ n))^2) 1
      (q (s (φ n))).beta (q (s (φ n))).tau (q (s (φ n))).stepSize)/ε (s (φ n))<a := by
    simpa only [hFe,hFq,Function.comp_def] using hn
  exact (not_lt_of_ge hbadn) hgood

/-- The source's literal quadratic limsup ceiling for every accelerated family. -/
theorem accelerated_quadratic_limsup {A : Type*} {l : Filter A} [NeBot l]
    [l.IsCountablyGenerated] {ε : A→ℝ} {q : A→Momentum.Tuning} {c : ℝ}
    (hc : 0<c) (he : Tendsto ε l (𝓝[>] (0:ℝ)))
    (hfull : ∀ᶠ n in l,Momentum.momentumRate (q n).beta (q n).tau (q n).stepSize
      (q n).step_pos.ne' (ε n^2) 1≤1-c*ε n) :
    limsup (fun n=>((1-Quadratic.quadraticRate (ε n^2) 1
      (q n).beta (q n).tau (q n).stepSize)/ε n:EReal)) l≤(Real.sqrt 2:EReal) := by
  by_contra hh
  obtain ⟨a,ha,halim⟩ := EReal.exists_between_coe_real (lt_of_not_ge hh)
  have hbound : ∀ᶠ n in l,((1-Quadratic.quadraticRate (ε n^2) 1
      (q n).beta (q n).tau (q n).stepSize)/ε n:EReal)≤(a:EReal) := by
    filter_upwards [accelerated_quadratic_eventually_lt hc he hfull (EReal.coe_lt_coe_iff.mp ha)] with n hn
    exact EReal.coe_le_coe_iff.mpr hn.le
  exact (not_lt_of_ge (Filter.limsup_le_of_le (by isBoundedDefault) hbound)) halim

end
end nesterov.TwoStep
