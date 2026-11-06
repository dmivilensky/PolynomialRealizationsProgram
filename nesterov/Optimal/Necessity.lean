import nesterov.Optimal.NecessityBounded
import nesterov.Optimal.ModerateDip
import nesterov.Optimal.DeepDip
import nesterov.Optimal.Sufficiency

/-! Necessity of the moving lag-one minimum, including every unbounded approach. -/
namespace nesterov.TwoStep.Scaling
noncomputable section
open Filter
open scoped Topology

private theorem impossible_optimal_of_rest_lower {A : Type*} {l : Filter A} [NeBot l]
    (F : Scaling A l 3 2 (1/2)) {c : ℝ} (hc : c<1)
    (hfull : Tendsto F.fullCoefficientAt l (𝓝 1))
    (hrest : ∀ᶠ p in l,1-c*F.epsilon p≤Momentum.momentumRestRate
      (F.tuning p).beta (F.tuning p).tau (F.tuning p).stepSize
      (F.tuning p).step_pos.ne' (F.epsilon p^2) 1) : False := by
  have hbound : ∀ᶠ p in l,F.fullCoefficientAt p≤c := by
    filter_upwards [hrest,F.epsilon_pos,F.layer_coefficients_order] with p hp he ho
    apply ho.trans
    apply (div_le_iff₀ he).mpr
    change 1-Momentum.momentumRestRate (F.tuning p).beta (F.tuning p).tau
      (F.tuning p).stepSize (F.tuning p).step_pos.ne' (F.epsilon p^2) 1≤c*F.epsilon p
    linarith
  exact (not_lt_of_ge (le_of_tendsto hfull hbound)) hc

private theorem frequently_bounded_of_not_atTop {A : Type*} {l : Filter A} {f : A→ℝ}
    (hn : ¬Tendsto f l atTop) : ∃ M : ℝ,∃ᶠ p in l,f p<M := by
  simpa only [tendsto_atTop,not_forall,not_eventually,not_le] using hn

private theorem no_positive_defect_sequence (F : Scaling ℕ atTop 3 2 (1/2))
    {q : ℝ} (hq : 0<q) (hq1 : q≤1)
    (hstable : ∀ᶠ p in atTop,(F.tuning p).Stable (F.epsilon p^2) 1)
    (hfull : Tendsto F.fullCoefficientAt atTop (𝓝 1))
    (hlo : ∀ᶠ p in atTop,q≤F.cornerCriterionRatio p) : False := by
  by_cases hd : Tendsto F.cornerDefect atTop atTop
  · by_cases hr : Tendsto F.cornerCriterionRatio atTop atTop
    · have hi := tendsto_inv_atTop_zero.comp hr
      have hdepth : Tendsto (fun p=>(F.stabilityMargin p+5+F.cornerDefect p)/F.cornerDefect p^2)
          atTop (𝓝 0) := by
        apply hi.congr'
        exact Eventually.of_forall fun p=>by simp only [Function.comp_def,cornerCriterionRatio,inv_div]
      have hdiv := F.corner_deep_dip_divergence hd hdepth hstable
      apply impossible_optimal_of_rest_lower F (c:=0) (by norm_num) hfull
      filter_upwards [hdiv] with p hp
      obtain ⟨K,hK⟩ := hp
      simpa only [zero_mul,sub_zero] using hK.2.2.2.le
    · obtain ⟨M,hfreq⟩ := frequently_bounded_of_not_atTop hr
      obtain ⟨s,hs,hbs⟩ := exists_seq_forall_of_frequently hfreq
      let G : Scaling ℕ atTop 3 2 (1/2) := F.reindex s hs
      have hGs : ∀ᶠ p in atTop,(G.tuning p).Stable (G.epsilon p^2) 1 := hs.eventually hstable
      have hGfull : Tendsto G.fullCoefficientAt atTop (𝓝 1) := hfull.comp hs
      have hGd : Tendsto G.cornerDefect atTop atTop := hd.comp hs
      have hGlo : ∀ᶠ p in atTop,q≤G.cornerCriterionRatio p := hs.eventually hlo
      have hGhi : ∀ᶠ p in atTop,G.cornerCriterionRatio p≤M := Eventually.of_forall fun p=>(hbs p).le
      exact impossible_optimal_of_rest_lower G (by linarith : 1-q/48<1) hGfull
        (G.corner_moderate_dip_rest_lower hq hq1 hGd hGlo hGhi hGs)
  · obtain ⟨M,hfreq⟩ := frequently_bounded_of_not_atTop hd
    obtain ⟨s,hs,hbs⟩ := exists_seq_forall_of_frequently hfreq
    let G : Scaling ℕ atTop 3 2 (1/2) := F.reindex s hs
    exact G.corner_no_bounded_defect_bad_sequence hq (hs.eventually hstable) (hfull.comp hs)
      (hs.eventually hlo) (Eventually.of_forall fun p=>(hbs p).le)

variable {A : Type*} {l : Filter A} (F : Scaling A l 3 2 (1/2))

theorem corner_criterion_tendsto_of_full_optimal [l.IsCountablyGenerated]
    (hstable : ∀ᶠ p in l,(F.tuning p).Stable (F.epsilon p^2) 1)
    (hfull : Tendsto F.fullCoefficientAt l (𝓝 1)) :
    Tendsto F.cornerCriterionRatio l (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro c hc
    exact ((F.corner_denominator_pos hstable).mono fun p hp=>by
      have hnon : 0≤F.cornerCriterionRatio p := div_nonneg (sq_nonneg _) hp.le
      exact hc.trans_le hnon)
  · intro c hc
    by_contra hn
    have hfreq : ∃ᶠ p in l,c≤F.cornerCriterionRatio p := by
      simpa only [not_eventually,not_lt] using hn
    obtain ⟨s,hs,hbs⟩ := exists_seq_forall_of_frequently hfreq
    let G : Scaling ℕ atTop 3 2 (1/2) := F.reindex s hs
    let q : ℝ := min c 1
    have hq : 0<q := lt_min hc (by norm_num)
    have hq1 : q≤1 := min_le_right _ _
    apply no_positive_defect_sequence G hq hq1 (hs.eventually hstable) (hfull.comp hs)
    exact Eventually.of_forall fun p=>(min_le_left c 1).trans (hbs p)

theorem optimal_lag_minimum_necessary [l.IsCountablyGenerated] [NeBot l]
    (hstable : ∀ᶠ p in l,(F.tuning p).Stable (F.epsilon p^2) 1)
    (hfull : Tendsto F.fullCoefficientAt l (𝓝 1)) :
    Tendsto F.cornerLagAt l (𝓝 1) :=
  F.corner_lag_tendsto_of_criterion (F.corner_margin_liminf_of_full_optimal hstable hfull)
    (F.corner_criterion_tendsto_of_full_optimal hstable hfull)

theorem optimal_lag_minimum_iff [l.IsCountablyGenerated] [NeBot l]
    (hstable : ∀ᶠ p in l,(F.tuning p).Stable (F.epsilon p^2) 1) :
    Tendsto F.fullCoefficientAt l (𝓝 1) ↔ Tendsto F.cornerLagAt l (𝓝 1) :=
  ⟨F.optimal_lag_minimum_necessary hstable,
    fun h=>(F.optimal_coefficients_tendsto hstable h).1⟩

theorem optimal_actual_ratio_iff [l.IsCountablyGenerated] [NeBot l]
    (hstable : ∀ᶠ p in l,(F.tuning p).Stable (F.epsilon p^2) 1) :
    Tendsto F.fullCoefficientAt l (𝓝 1) ↔
      (7:EReal)≤liminf (fun p=>(F.stabilityMargin p:EReal)) l ∧
        Tendsto F.cornerCriterionRatio l (𝓝 0) :=
  (F.optimal_lag_minimum_iff hstable).trans (F.corner_ratio_criterion_iff hstable)

end
end nesterov.TwoStep.Scaling
