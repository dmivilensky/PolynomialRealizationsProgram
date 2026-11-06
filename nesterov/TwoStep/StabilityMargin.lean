import nesterov.TwoStep.AlternatingAsymptotics

/-! Exact finite-parameter and limiting stability tests for the scaled margin. -/
namespace nesterov.TwoStep.Scaling
noncomputable section
open Filter
open scoped Topology
variable {A : Type*} {l : Filter A} {θ y τ : ℝ} (F : Scaling A l θ y τ)

theorem stable_iff_scaled_margin :
    ∀ᶠ a in l, (F.tuning a).Stable (F.epsilon a^2) 1 ↔
      2*F.thetaAt a < F.stabilityMargin a := by
  filter_upwards [F.epsilon_pos,F.epsilon_zero.eventually
    (eventually_lt_nhds (by norm_num : (0:ℝ)<1)),F.stability_gap_exact] with a he he1 hg
  rw [(F.tuning a).stable_iff (sq_pos_of_pos he) (by nlinarith : F.epsilon a^2<1)]
  simp only [mul_one]
  have heq : 2*(1+(F.tuning a).beta)-(F.tuning a).stepSize*(1+2*(F.tuning a).tau)=
      (F.stabilityMargin a-2*F.thetaAt a)*F.epsilon a := by
    simpa only [largestCurvatureGap_eq] using hg
  constructor
  · intro hs
    have hp : 0<(F.stabilityMargin a-2*F.thetaAt a)*F.epsilon a := by linarith
    exact sub_pos.mp ((mul_pos_iff_of_pos_right he).mp hp)
  · intro hs
    have hp := mul_pos (sub_pos.mpr hs) he
    linarith

theorem eventually_stable_of_margin_limit {s : ℝ}
    (hs : Tendsto F.stabilityMargin l (𝓝 s)) (hθs : 2*θ<s) :
    ∀ᶠ a in l, (F.tuning a).Stable (F.epsilon a^2) 1 := by
  have hd := (hs.sub (F.theta_tendsto.const_mul 2)).eventually
    (eventually_gt_nhds (sub_pos.mpr hθs))
  filter_upwards [F.stable_iff_scaled_margin,hd] with a ha hd
  exact ha.mpr (sub_pos.mp hd)

theorem eventually_unstable_of_margin_limit {s : ℝ}
    (hs : Tendsto F.stabilityMargin l (𝓝 s)) (hsθ : s<2*θ) :
    ∀ᶠ a in l, ¬(F.tuning a).Stable (F.epsilon a^2) 1 := by
  have hd := (hs.sub (F.theta_tendsto.const_mul 2)).eventually
    (eventually_lt_nhds (sub_neg.mpr hsθ))
  filter_upwards [F.stable_iff_scaled_margin,hd] with a ha hd
  change F.stabilityMargin a-2*F.thetaAt a<0 at hd
  intro hstable
  have hp := ha.mp hstable
  linarith

theorem eventually_stable_of_margin_atTop
    (hs : Tendsto F.stabilityMargin l atTop) :
    ∀ᶠ a in l, (F.tuning a).Stable (F.epsilon a^2) 1 := by
  filter_upwards [F.stable_iff_scaled_margin,hs.eventually_ge_atTop (2*θ+2),
    F.theta_tendsto.eventually (eventually_lt_nhds (show θ<θ+1 by linarith))]
    with a ha hs hθ
  change F.thetaAt a<θ+1 at hθ
  exact ha.mpr (by linarith)

end
end nesterov.TwoStep.Scaling
