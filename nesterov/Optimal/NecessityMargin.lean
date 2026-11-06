import nesterov.Optimal.RatioCriterion
import nesterov.Corner.Roots
import nesterov.Layer.ResultsRates

/-! Optimality forces the alternating margin without any bounded-margin assumption. -/
namespace nesterov.TwoStep.Scaling
noncomputable section
open Filter
open scoped Topology
variable {A : Type*} {l : Filter A} (F : Scaling A l 3 2 (1/2))

def cornerAlternatingFactor (p : A) : ℝ :=
  2/(2+Quadratic.S (F.tuning p).beta (F.tuning p).tau (F.tuning p).stepSize 1+
    Real.sqrt ((2+Quadratic.S (F.tuning p).beta (F.tuning p).tau (F.tuning p).stepSize 1)^2-
      4*largestCurvatureGap (F.tuning p)))

theorem corner_alternating_factor_tendsto : Tendsto F.cornerAlternatingFactor l (𝓝 1) := by
  have he := F.boundary_gap_tendsto (by norm_num : (2:ℝ)*(1+2*(1/2))=4)
  have hs : Tendsto (fun p=>2+Quadratic.S (F.tuning p).beta (F.tuning p).tau
      (F.tuning p).stepSize 1) l (𝓝 1) := by
    convert F.corner_S_tendsto.const_add 2 using 1
    norm_num
  have hdisc := ((hs.pow 2).sub (he.const_mul 4)).sqrt
  have hden := hs.add hdisc
  have h := (tendsto_const_nhds (x:=(2:ℝ))).div hden (by norm_num : (1:ℝ)+Real.sqrt (1^2-4*0)≠0)
  convert h using 1
  · rfl
  · norm_num

theorem corner_alternating_factor_exact : ∀ᶠ p in l,
    alternatingShift (F.tuning p)/F.epsilon p=
      F.cornerAlternatingFactor p*(F.stabilityMargin p-2*F.thetaAt p) := by
  filter_upwards [F.epsilon_pos,F.stability_gap_scaled_exact] with p he hg
  unfold alternatingShift alternatingDelta cornerAlternatingFactor
  rw [←hg]
  ring

theorem corner_margin_lower_of_full_optimal
    (hstable : ∀ᶠ p in l,(F.tuning p).Stable (F.epsilon p^2) 1) :
    ∀ᶠ p in l,F.fullCoefficientAt p/F.cornerAlternatingFactor p+2*F.thetaAt p≤F.stabilityMargin p := by
  have ha := F.alternating_rate_lower (by norm_num : (1:ℝ)/2≤1/2)
    (by norm_num : (2:ℝ)*(1+2*(1/2))=4) hstable
  filter_upwards [ha,F.epsilon_pos,F.layer_coefficients_order,F.corner_alternating_factor_exact,
    F.corner_alternating_factor_tendsto.eventually (eventually_gt_nhds (by norm_num : (0:ℝ)<1))]
    with p ha he ho hfactor hf
  have hrest : F.restCoefficientAt p≤alternatingShift (F.tuning p)/F.epsilon p :=
    div_le_div_of_nonneg_right (by
      change 1-Momentum.momentumRestRate (F.tuning p).beta (F.tuning p).tau
        (F.tuning p).stepSize (F.tuning p).step_pos.ne' (F.epsilon p^2) 1≤alternatingShift (F.tuning p)
      linarith [ha.2.1]) he.le
  have h := ho.trans hrest
  rw [hfactor] at h
  have hdiv : F.fullCoefficientAt p/F.cornerAlternatingFactor p≤F.stabilityMargin p-2*F.thetaAt p :=
    (div_le_iff₀ hf).mpr (by nlinarith [h])
  linarith

theorem corner_margin_liminf_of_full_optimal [NeBot l]
    (hstable : ∀ᶠ p in l,(F.tuning p).Stable (F.epsilon p^2) 1)
    (hfull : Tendsto F.fullCoefficientAt l (𝓝 1)) :
    (7:EReal)≤liminf (fun p=>(F.stabilityMargin p:EReal)) l := by
  have h := (hfull.div F.corner_alternating_factor_tendsto (by norm_num : (1:ℝ)≠0)).add
    (F.theta_tendsto.const_mul 2)
  have h7 : Tendsto (fun p=>((F.fullCoefficientAt p/F.cornerAlternatingFactor p+2*F.thetaAt p:ℝ):EReal))
      l (𝓝 (7:EReal)) := by
    apply EReal.tendsto_coe.mpr
    convert h using 1 <;> norm_num [thetaAt]
  rw [←h7.liminf_eq]
  exact Filter.liminf_le_liminf ((F.corner_margin_lower_of_full_optimal hstable).mono fun _ h=>
    EReal.coe_le_coe_iff.mpr h)

end
end nesterov.TwoStep.Scaling
