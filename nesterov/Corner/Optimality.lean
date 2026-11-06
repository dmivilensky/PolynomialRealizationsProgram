import nesterov.Corner.Rates
import nesterov.Corner.Regions
import nesterov.Flow.Damping

/-! Necessity and sufficiency of the exact optimal corner wedge for actual rates. -/
namespace nesterov.TwoStep.Scaling
noncomputable section
open Filter
open scoped Topology
variable {A : Type*} {l : Filter A} [l.IsCountablyGenerated] [NeBot l]
variable {θ : ℝ} (F : Scaling A l θ 2 (1/2))

omit [NeBot l] in
/-- Every corner family outside the optimal wedge has both upper limiting
acceleration coefficients strictly below one. -/
theorem corner_suboptimal_limsup_lt_one {a b : ℝ}
    (ha : Tendsto F.cornerA l (𝓝 a)) (hb : Tendsto F.cornerB l (𝓝 b))
    (hmargin : θ<2*a+b) (hnot : ¬(θ=3 ∧ a≤5/4 ∧ 7/2≤2*a+b)) :
    limsup (fun p=>(F.fullCoefficientAt p:EReal)) l<1 ∧
      limsup (fun p=>(F.restCoefficientAt p:EReal)) l<1 := by
  have hmin : min (Flow.cQ θ 2) (Corner.cDisc θ a b)<1 := by
    by_cases hθ : θ=3
    · subst θ
      have hdisc : Corner.cDisc 3 a b<1 := by
        by_contra hn
        exact hnot ⟨rfl,Corner.one_le_cDisc_iff.mp (le_of_not_gt hn)⟩
      exact (min_le_right _ _).trans_lt hdisc
    · have hcF : Flow.cF θ 2<1 := by
        have hle : Flow.cF θ 2≤1 := by
          simpa using (Flow.cF_le_optimal (θ:=θ) (by norm_num : (0:ℝ)<2))
        apply lt_of_le_of_ne hle
        intro heq
        have heq' : Flow.cF θ 2=Real.sqrt (2/2) := by simpa using heq
        have hh := (Flow.cF_eq_optimal_iff (by norm_num : (0:ℝ)<2)).mp heq'
        exact hθ (by simpa using hh)
      have hdisc : Corner.cDisc θ a b≤θ/3 :=
        (Corner.cDisc_endpoints θ a b).trans (min_le_left _ _)
      have hbound : min (Flow.cQ θ 2) (Corner.cDisc θ a b)≤Flow.cF θ 2 :=
        le_min ((min_le_right _ _).trans hdisc) (min_le_left _ _)
      exact hbound.trans_lt hcF
  have hmin' : min (Flow.cQ θ 2:EReal) (Corner.cDisc θ a b:EReal)<1 := by
    rcases min_lt_iff.mp hmin with hq|hd
    · exact (min_le_left _ _).trans_lt (by exact_mod_cast hq)
    · exact (min_le_right _ _).trans_lt (by exact_mod_cast hd)
  have hmax' : (max 0 (min (Flow.cQ θ 2) (Corner.cDisc θ a b)):EReal)<1 := by
    exact max_lt (by norm_num) hmin'
  have h := F.corner_coefficient_limsup_upper ha hb hmargin
  exact ⟨h.1.trans_lt hmax',h.2.trans_lt hmax'⟩

theorem corner_theta_eq_three_of_optimal {a b : ℝ}
    (ha : Tendsto F.cornerA l (𝓝 a)) (hb : Tendsto F.cornerB l (𝓝 b))
    (hmargin : θ<2*a+b) (hfull : Tendsto F.fullCoefficientAt l (𝓝 1)) : θ=3 := by
  have hs := F.corner_eventually_stable ha hb hmargin
  have hge : 1≤Flow.cF θ 2 := by
    by_contra hn
    obtain ⟨c,hc,hc1⟩ := exists_between (lt_of_not_ge hn)
    have hbound : ∀ᶠ p in l,F.fullCoefficientAt p≤c := by
      filter_upwards [F.rest_coefficient_eventually_le_filter hs hc,F.layer_coefficients_order] with p hp ho
      exact ho.trans hp
    exact (not_lt_of_ge (le_of_tendsto hfull hbound)) hc1
  have hle : Flow.cF θ 2≤1 := by
    simpa using (Flow.cF_le_optimal (θ:=θ) (by norm_num : (0:ℝ)<2))
  have he : Flow.cF θ 2=Real.sqrt (2/2) := by simpa using le_antisymm hle hge
  simpa using (Flow.cF_eq_optimal_iff (by norm_num : (0:ℝ)<2)).mp he

theorem corner_optimal_iff {a b : ℝ}
    (ha : Tendsto F.cornerA l (𝓝 a)) (hb : Tendsto F.cornerB l (𝓝 b))
    (hmargin : θ<2*a+b) :
    Tendsto F.fullCoefficientAt l (𝓝 1) ↔ θ=3 ∧ a≤5/4 ∧ 7/2≤2*a+b := by
  constructor
  · intro hfull
    have hθ := F.corner_theta_eq_three_of_optimal ha hb hmargin hfull
    subst θ
    have hdisc : 1≤Corner.cDisc 3 a b := by
      by_contra hn
      have hd : Corner.cDisc 3 a b<1 := lt_of_not_ge hn
      have hq : Flow.cQ 3 2=1 := by norm_num [Flow.cQ]
      have hthreshold : max 0 (min (Flow.cQ 3 2) (Corner.cDisc 3 a b))<1 := by
        rw [hq]
        exact max_lt (by norm_num) ((min_le_right _ _).trans_lt hd)
      obtain ⟨c,hc,hc1⟩ := exists_between hthreshold
      have hrest := F.corner_rest_lower ha hb hmargin hc
      have hupper : ∀ᶠ p in l,F.fullCoefficientAt p<c := by
        filter_upwards [hrest,F.epsilon_pos,F.layer_coefficients_order] with p hp he ho
        apply ho.trans_lt
        apply (div_lt_iff₀ he).mpr
        change 1-Momentum.momentumRestRate (F.tuning p).beta (F.tuning p).tau
          (F.tuning p).stepSize (F.tuning p).step_pos.ne' (F.epsilon p^2) 1<c*F.epsilon p
        linarith
      have hlower := hfull.eventually (eventually_gt_nhds hc1)
      obtain ⟨p,hp,hp'⟩ := (hupper.and hlower).exists
      exact (not_lt_of_ge hp.le) hp'
    exact ⟨rfl,Corner.one_le_cDisc_iff.mp hdisc⟩
  · rintro ⟨rfl,haa,hbb⟩
    have hmins := Corner.optimal_wedge_minima haa hbb
    have hq : Flow.cQ 3 2=1 := by norm_num [Flow.cQ]
    have hLag : 0<Corner.cLag 3 a b := by rw [hmins.1];norm_num
    have heq : min (Flow.cQ 3 2) (Corner.cLag 3 a b)=min (Flow.cQ 3 2) (Corner.cDisc 3 a b) := by
      rw [hmins.1,hmins.2]
    have h := (F.corner_coefficients_tendsto ha hb hmargin hLag heq).1
    simpa only [hq,hmins.1,min_self] using h

omit [NeBot l] in
theorem corner_rest_optimal_of_wedge {a b : ℝ} (hθ : θ=3)
    (ha : Tendsto F.cornerA l (𝓝 a)) (hb : Tendsto F.cornerB l (𝓝 b))
    (haa : a≤5/4) (hbb : 7/2≤2*a+b) :
    Tendsto F.fullCoefficientAt l (𝓝 1) ∧ Tendsto F.restCoefficientAt l (𝓝 1) := by
  subst θ
  have hmins := Corner.optimal_wedge_minima haa hbb
  have hq : Flow.cQ 3 2=1 := by norm_num [Flow.cQ]
  have h := F.corner_coefficients_tendsto ha hb (by linarith : (3:ℝ)<2*a+b)
    (by rw [hmins.1];norm_num : 0<Corner.cLag 3 a b) (by rw [hmins.1,hmins.2])
  simpa only [hq,hmins.1,min_self] using h

end
end nesterov.TwoStep.Scaling
