import nesterov.Optimal.Necessity
import nesterov.Corner.Model

/-! The source consequence for steps approaching the corner more slowly than epsilon. -/
namespace nesterov.TwoStep.Scaling
noncomputable section
open Filter
open scoped Topology
variable {A : Type*} {l : Filter A} (F : Scaling A l 3 2 (1/2))

theorem corner_margin_coordinates_exact : ∀ᶠ p in l,
    F.stabilityMargin p=2*F.cornerB p+4*F.cornerAlpha p := by
  filter_upwards [F.epsilon_pos] with p hp
  unfold stabilityMargin cornerB cornerAlpha
  field_simp
  ring

theorem corner_margin_atTop_of_beyond
    (hb : Tendsto F.cornerB l atTop)
    (hα : ∃ M : ℝ,∀ᶠ p in l,|F.cornerAlpha p|≤M) :
    Tendsto F.stabilityMargin l atTop := by
  obtain ⟨M,hM⟩ := hα
  apply tendsto_atTop.mpr
  intro R
  filter_upwards [hM,hb.eventually_ge_atTop ((R+4*M)/2),F.corner_margin_coordinates_exact]
    with p hp hb he
  have ha := (abs_le.mp hp).1
  rw [he]
  linarith

theorem corner_ratio_tendsto_of_beyond
    (hb : Tendsto F.cornerB l atTop)
    (hα : ∃ M : ℝ,∀ᶠ p in l,|F.cornerAlpha p|≤M) :
    Tendsto F.cornerCriterionRatio l (𝓝 0) := by
  obtain ⟨M,hM⟩ := hα
  let C : ℝ := 4*|M|+5
  have hC : 0<C := by dsimp [C];positivity
  have hdef : ∀ᶠ p in l,0≤F.cornerDefect p ∧ F.cornerDefect p≤C := by
    filter_upwards [hM] with p hp
    refine ⟨F.corner_defect_nonneg p,?_⟩
    have ha := (abs_le.mp hp).2
    unfold cornerDefect
    apply max_le
    · dsimp [C]
      linarith [le_abs_self M]
    · exact hC.le
  have hm := F.corner_margin_atTop_of_beyond hb ⟨M,hM⟩
  have hden : Tendsto (fun p=>F.stabilityMargin p+5+F.cornerDefect p) l atTop := by
    apply tendsto_atTop.mpr
    intro R
    filter_upwards [hm.eventually_ge_atTop (R-5)] with p hp
    linarith [F.corner_defect_nonneg p]
  have hzero := (tendsto_inv_atTop_zero.comp hden).const_mul (C^2)
  have hbounds : ∀ᶠ p in l,0≤F.cornerCriterionRatio p ∧
      F.cornerCriterionRatio p≤C^2*(F.stabilityMargin p+5+F.cornerDefect p)⁻¹ := by
    filter_upwards [hdef,hden.eventually_gt_atTop 0] with p hp hd
    refine ⟨div_nonneg (sq_nonneg _) hd.le,?_⟩
    unfold cornerCriterionRatio
    rw [←div_eq_mul_inv]
    apply div_le_div_of_nonneg_right _ hd.le
    nlinarith
  exact squeeze_zero' (hbounds.mono fun _ h=>h.1) (hbounds.mono fun _ h=>h.2)
    (by simpa only [Function.comp_def,mul_zero] using hzero)

theorem optimal_beyond_corner [l.IsCountablyGenerated]
    (hb : Tendsto F.cornerB l atTop)
    (hα : ∃ M : ℝ,∀ᶠ p in l,|F.cornerAlpha p|≤M) :
    Tendsto F.fullCoefficientAt l (𝓝 1) ∧ Tendsto F.restCoefficientAt l (𝓝 1) := by
  have hm := F.corner_margin_atTop_of_beyond hb hα
  have hs := F.eventually_stable_of_margin_atTop hm
  have hmargin : (7:EReal)≤liminf (fun p=>(F.stabilityMargin p:EReal)) l :=
    Filter.le_liminf_of_le (by isBoundedDefault)
      ((hm.eventually_ge_atTop 7).mono fun _ hp=>EReal.coe_le_coe_iff.mpr hp)
  exact F.optimal_coefficients_tendsto hs (F.corner_lag_tendsto_of_criterion hmargin
    (F.corner_ratio_tendsto_of_beyond hb hα))

end
end nesterov.TwoStep.Scaling
