import nesterov.TwoStep.FrontierAcceleration
import nesterov.TwoStep.Kappa
import nesterov.Flow.Damping

/-! No Nesterov family beats the class-optimal leading constant. The tunings
need not have parameter limits, and unstable tunings are allowed. -/
namespace nesterov.TwoStep
noncomputable section
open Filter Set
open scoped Topology
variable {A : Type*} {l : Filter A} [l.IsCountablyGenerated]
  {ε : A → ℝ} {q : A → Momentum.Tuning}

theorem nesterov_full_coefficient_eventually_lt
    (he : Tendsto ε l (𝓝[>] (0:ℝ)))
    (hτ : ∀ᶠ a in l, (q a).tau=(q a).beta)
    {b : ℝ} (hb : Real.sqrt (2/3)<b) :
    ∀ᶠ a in l, tuningFullCoefficient (ε a) (q a)<b := by
  by_contra hn
  have hbad : ∃ᶠ a in l, b≤tuningFullCoefficient (ε a) (q a) := by
    simpa only [not_eventually,not_lt] using hn
  obtain ⟨s,hsl,hbadS⟩ := exists_seq_forall_of_frequently hbad
  have hb0 : 0<b := (Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<2/3)).trans hb
  have heS := he.comp hsl
  have hfullS : ∀ᶠ n in atTop,
      Momentum.momentumRate (q (s n)).beta (q (s n)).tau (q (s n)).stepSize
        (q (s n)).step_pos.ne' (ε (s n)^2) 1≤1-b*ε (s n) := by
    filter_upwards [heS.eventually self_mem_nhdsWithin] with n hn
    have hp : 0<ε (s n) := hn
    have hh := (le_div_iff₀ hp).mp (hbadS n)
    linarith
  have hcontrols := full_acceleration_controls hb0 heS hfullS
  have hsS := hcontrols.mono fun _ h => h.1
  have hqS := hcontrols.mono fun _ h => h.2.1
  obtain ⟨φ,hφ,θ,y,τ,_,_,_,hm,F,hFe,hFq⟩ :=
    accelerated_subsequence hb0 heS hsS hqS
  have hsF : ∀ᶠ n in atTop, (F.tuning n).Stable (F.epsilon n^2) 1 := by
    simpa only [hFe,hFq,Function.comp_def] using hφ.tendsto_atTop.eventually hsS
  have hτF : ∀ᶠ n in atTop, (F.tuning n).tau=(F.tuning n).beta := by
    simpa only [hFq,Function.comp_def] using
      hφ.tendsto_atTop.eventually (hsl.eventually hτ)
  have hτone : Tendsto (fun n => (F.tuning n).tau) atTop (𝓝 1) :=
    F.beta_tendsto.congr' (hτF.mono fun _ h => h.symm)
  have hτeq : τ=1 := tendsto_nhds_unique F.tau_tendsto hτone
  rw [hτeq] at hm
  have hcf : Flow.cF θ y≤Real.sqrt (2/3) :=
    (Flow.cF_le_optimal F.step_pos).trans
      (Real.sqrt_le_sqrt (by nlinarith : y/2≤2/3))
  obtain ⟨d,hd,hdb⟩ := exists_between (hcf.trans_lt hb)
  obtain ⟨n,hn⟩ := (F.full_coefficient_eventually_le_filter hsF hd).exists
  have hbn : b≤F.fullCoefficientAt n := by
    simpa only [Scaling.fullCoefficientAt,hFe,hFq,Function.comp_def,
      tuningFullCoefficient] using hbadS (φ n)
  exact (not_lt_of_ge hbn) (hn.trans_lt hdb)

/-- The literal limsup statement also excludes a larger positive constant when
the original tuning parameters oscillate or some family members are unstable. -/
theorem nesterov_full_coefficient_limsup
    (he : Tendsto ε l (𝓝[>] (0:ℝ)))
    (hτ : ∀ᶠ a in l, (q a).tau=(q a).beta) :
    limsup (fun a => (tuningFullCoefficient (ε a) (q a):EReal)) l≤
      (Real.sqrt (2/3):EReal) := by
  by_contra hn
  obtain ⟨b,hb,hblim⟩ := EReal.exists_between_coe_real (lt_of_not_ge hn)
  have hbound : ∀ᶠ a in l, (tuningFullCoefficient (ε a) (q a):EReal)≤(b:EReal) := by
    filter_upwards [nesterov_full_coefficient_eventually_lt he hτ
      (EReal.coe_lt_coe_iff.mp hb)] with a ha
    exact EReal.coe_le_coe_iff.mpr ha.le
  exact (not_lt_of_ge (Filter.limsup_le_of_le (by isBoundedDefault) hbound)) hblim

/-- The same universal ceiling in the article's literal condition number. -/
theorem nesterov_full_kappa_limsup {q : ℝ → Momentum.Tuning}
    (hτ : ∀ᶠ κ in atTop, (q κ).tau=(q κ).beta) :
    limsup (fun κ => (Real.sqrt κ*(1-Momentum.momentumRate (q κ).beta
      (q κ).tau (q κ).stepSize (q κ).step_pos.ne' (1/κ) 1):EReal)) atTop≤
      (Real.sqrt (2/3):EReal) := by
  have h := nesterov_full_coefficient_limsup Slow.epsilon_tendsto hτ
  calc
    _ = limsup (fun κ => (tuningFullCoefficient (Slow.epsilon κ) (q κ):EReal)) atTop := by
      apply limsup_congr
      filter_upwards [eventually_gt_atTop (0:ℝ)] with κ hκ
      unfold tuningFullCoefficient
      rw [Slow.epsilon_sq hκ.le,Slow.coefficient_kappa hκ]
      simp only [EReal.coe_mul,EReal.coe_sub,EReal.coe_one]
    _ ≤ _ := h

end
end nesterov.TwoStep
