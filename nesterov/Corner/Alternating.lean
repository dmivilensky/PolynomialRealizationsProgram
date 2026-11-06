import nesterov.Corner.Model
import nesterov.TwoStep.SequenceCeiling

/-! The alternating endpoint obstruction in the corner is the actual
largest-curvature quadratic trajectory from rest. -/
namespace nesterov.TwoStep.Scaling
noncomputable section
open Filter
open scoped Topology
variable {A : Type*} {l : Filter A} {θ : ℝ} (F : Scaling A l θ 2 (1/2))

theorem corner_alternating_coefficient_lt {a b c : ℝ}
    (ha : Tendsto F.cornerA l (𝓝 a)) (hb : Tendsto F.cornerB l (𝓝 b))
    (hmargin : θ<2*a+b) (hc : Corner.cpi θ a b<c) :
    ∀ᶠ p in l,F.restCoefficientAt p<c := by
  have hs := F.corner_eventually_stable ha hb hmargin
  have hshift := F.alternating_shift_scaled_tendsto (by norm_num : (1/2:ℝ)≤1/2)
    (by norm_num : (2:ℝ)*(1+2*(1/2))=4) hs (F.corner_margin_tendsto ha hb)
  have he : alternatingConstant θ (1/2) (4*a+2*b)=Corner.cpi θ a b := by
    unfold alternatingConstant Corner.cpi
    norm_num
    ring
  rw [he] at hshift
  have hmode := F.alternating_rate_lower (by norm_num : (1/2:ℝ)≤1/2)
    (by norm_num : (2:ℝ)*(1+2*(1/2))=4) hs
  filter_upwards [hmode,F.epsilon_pos,hshift.eventually (eventually_lt_nhds hc)]
    with p hp he hlim
  have hcoef : F.restCoefficientAt p≤alternatingShift (F.tuning p)/F.epsilon p :=
    div_le_div_of_nonneg_right (by linarith only [hp.2.1]) he.le
  exact hcoef.trans_lt hlim

theorem corner_alternating_rest_lower {a b c : ℝ}
    (ha : Tendsto F.cornerA l (𝓝 a)) (hb : Tendsto F.cornerB l (𝓝 b))
    (hmargin : θ<2*a+b) (hc : Corner.cpi θ a b<c) :
    ∀ᶠ p in l,1-c*F.epsilon p<Momentum.momentumRestRate
      (F.tuning p).beta (F.tuning p).tau (F.tuning p).stepSize
      (F.tuning p).step_pos.ne' (F.epsilon p^2) 1 := by
  filter_upwards [F.corner_alternating_coefficient_lt ha hb hmargin hc,F.epsilon_pos]
    with p hp he
  have hh := (div_lt_iff₀ he).mp hp
  change 1-Momentum.momentumRestRate (F.tuning p).beta (F.tuning p).tau
    (F.tuning p).stepSize (F.tuning p).step_pos.ne' (F.epsilon p^2) 1<c*F.epsilon p at hh
  linarith

end
end nesterov.TwoStep.Scaling
