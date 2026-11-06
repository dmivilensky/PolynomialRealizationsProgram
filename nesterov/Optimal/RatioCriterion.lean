import nesterov.Optimal.RatioBounds

/-! The exact unbounded-coordinate ratio criterion in the optimal-tuning theorem. -/
namespace nesterov.TwoStep.Scaling
noncomputable section
open Filter Set
open scoped Topology
variable {A : Type*} {l : Filter A} {y τ : ℝ} (F : Scaling A l 3 y τ)

def cornerCriterionRatio (p : A) : ℝ :=
  F.cornerDefect p^2/(F.stabilityMargin p+5+F.cornerDefect p)

theorem corner_numerator_reformulation (p : A) (ξ : ℝ) :
    Optimal.numerator (F.thetaAt p) (4*F.cornerAlpha p-5) (F.stabilityMargin p) ξ=
      F.cornerNAt p ξ := by
  unfold Optimal.numerator cornerNAt
  ring

theorem corner_criterion_eventual_bound
    (hstable : ∀ᶠ p in l,(F.tuning p).Stable (F.epsilon p^2) 1) :
    ∀ᶠ p in l,0≤F.cornerCriterionRatio p ∧
      F.cornerCriterionRatio p≤12*|1-F.cornerLagAt p|+24*|F.thetaAt p-3| := by
  filter_upwards [F.corner_denominator_pos hstable,F.stable_iff_scaled_margin,hstable,
    F.theta_tendsto.eventually (eventually_gt_nhds (by norm_num : (2:ℝ)<3))]
    with p hD hs hstab hθ
  change 2<F.thetaAt p at hθ
  have hm : 4≤F.stabilityMargin p := by have h := hs.mp hstab;linarith
  refine ⟨div_nonneg (sq_nonneg _) hD.le,?_⟩
  apply Optimal.ratio_defect_bound hm
  intro ξ hξ
  rw [F.corner_numerator_reformulation]
  exact F.cornerLagAt_le p hξ

theorem corner_criterion_tendsto_of_lag
    (hstable : ∀ᶠ p in l,(F.tuning p).Stable (F.epsilon p^2) 1)
    (hlag : Tendsto F.cornerLagAt l (𝓝 1)) :
    Tendsto F.cornerCriterionRatio l (𝓝 0) := by
  have h := (((tendsto_const_nhds (x:=(1:ℝ))).sub hlag).abs.const_mul 12).add
    ((F.theta_tendsto.sub (tendsto_const_nhds (x:=(3:ℝ)))).abs.const_mul 24)
  have hz : Tendsto (fun p=>12*|1-F.cornerLagAt p|+24*|F.thetaAt p-3|) l (𝓝 0) := by
    simpa only [thetaAt,sub_self,abs_zero,mul_zero,zero_add] using h
  exact squeeze_zero' ((F.corner_criterion_eventual_bound hstable).mono fun _ h=>h.1)
    ((F.corner_criterion_eventual_bound hstable).mono fun _ h=>h.2) hz

theorem corner_margin_liminf_of_lag [NeBot l]
    (hlag : Tendsto F.cornerLagAt l (𝓝 1)) :
    (7:EReal)≤liminf (fun p=>(F.stabilityMargin p:EReal)) l := by
  have h := hlag.add (F.theta_tendsto.const_mul 2)
  have h7 : Tendsto (fun p=>((F.cornerLagAt p+2*F.thetaAt p:ℝ):EReal)) l (𝓝 (7:EReal)) := by
    apply EReal.tendsto_coe.mpr
    convert h using 1 <;> norm_num [thetaAt]
  rw [←h7.liminf_eq]
  have hle : ∀ᶠ p in l,((F.cornerLagAt p+2*F.thetaAt p:ℝ):EReal)≤(F.stabilityMargin p:EReal) :=
    Eventually.of_forall fun p=>EReal.coe_le_coe_iff.mpr (by
      have h := F.cornerLagAt_le_margin p
      linarith)
  exact Filter.liminf_le_liminf hle

theorem corner_lag_tendsto_of_criterion
    (hmargin : (7:EReal)≤liminf (fun p=>(F.stabilityMargin p:EReal)) l)
    (hratio : Tendsto F.cornerCriterionRatio l (𝓝 0)) :
    Tendsto F.cornerLagAt l (𝓝 1) := by
  apply tendsto_order.mpr
  constructor
  · intro c hc
    let δ : ℝ := min 1 ((1-c)/16)
    have hδ : 0<δ := lt_min (by norm_num) (by linarith)
    have hδ1 : δ≤1 := min_le_left _ _
    have hcδ : c<1-8*δ := by
      have h := min_le_right 1 ((1-c)/16)
      change δ≤(1-c)/16 at h
      linarith
    have hclose : ∀ᶠ p in l,|F.thetaAt p-3|<δ := by
      have h := (F.theta_tendsto.sub (tendsto_const_nhds (x:=(3:ℝ)))).abs
      simp only [sub_self,abs_zero] at h
      exact h.eventually (eventually_lt_nhds hδ)
    have hmarg : ∀ᶠ p in l,7-δ<F.stabilityMargin p := by
      have hlt : ((7-δ:ℝ):EReal)<liminf (fun p=>(F.stabilityMargin p:EReal)) l :=
        (EReal.coe_lt_coe_iff.mpr (show (7-δ:ℝ)<7 by linarith)).trans_le hmargin
      exact (Filter.eventually_lt_of_lt_liminf hlt).mono fun _ h=>EReal.coe_lt_coe_iff.mp h
    have hrr : 0<min δ (δ^2/24) := lt_min hδ (div_pos (sq_pos_of_pos hδ) (by norm_num))
    filter_upwards [hclose,hmarg,hratio.eventually (eventually_lt_nhds hrr)] with p ht hs hr
    apply hcδ.trans_le
    apply F.le_cornerLagAt p
    intro ξ hξ
    have h := Optimal.ratio_uniform_lower hξ hδ hδ1 ht.le hs.le hr.le
    simpa only [F.corner_numerator_reformulation,cornerRatioAt] using h
  · intro c hc
    have hθ : Tendsto (fun p=>F.thetaAt p/3) l (𝓝 1) := by
      simpa only [thetaAt,div_self (by norm_num : (3:ℝ)≠0)] using F.theta_tendsto.div_const 3
    exact (hθ.eventually (eventually_lt_nhds hc)).mono fun p hp=>(F.cornerLagAt_le_theta p).trans_lt hp

theorem corner_ratio_criterion_iff [NeBot l]
    (hstable : ∀ᶠ p in l,(F.tuning p).Stable (F.epsilon p^2) 1) :
    Tendsto F.cornerLagAt l (𝓝 1) ↔
      (7:EReal)≤liminf (fun p=>(F.stabilityMargin p:EReal)) l ∧
        Tendsto F.cornerCriterionRatio l (𝓝 0) := by
  constructor
  · intro h
    exact ⟨F.corner_margin_liminf_of_lag h,F.corner_criterion_tendsto_of_lag hstable h⟩
  · rintro ⟨hm,hr⟩
    exact F.corner_lag_tendsto_of_criterion hm hr

end
end nesterov.TwoStep.Scaling
