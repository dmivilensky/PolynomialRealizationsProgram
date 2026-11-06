import nesterov.Corner.Resonant
import nesterov.Corner.Alternating

/-! The corner's discrete lower bound uses the attained discrete minimum,
the actual flow ceiling, alternating quadratic and rational spread witnesses. -/
namespace nesterov.TwoStep.Scaling
noncomputable section
open Filter Set
open scoped Topology
variable {A : Type*} {l : Filter A} {θ : ℝ} (F : Scaling A l θ 2 (1/2))

theorem corner_rest_lower [l.IsCountablyGenerated] {a b c : ℝ}
    (ha : Tendsto F.cornerA l (𝓝 a)) (hb : Tendsto F.cornerB l (𝓝 b))
    (hmargin : θ<2*a+b)
    (hc : max 0 (min (Flow.cQ θ 2) (Corner.cDisc θ a b))<c) :
    ∀ᶠ p in l,1-c*F.epsilon p<Momentum.momentumRestRate
      (F.tuning p).beta (F.tuning p).tau (F.tuning p).stepSize
      (F.tuning p).step_pos.ne' (F.epsilon p^2) 1 := by
  have hc0 : 0<c := (le_max_left _ _).trans_lt hc
  by_cases hflow : Flow.cF θ 2<c
  · obtain ⟨d,hd,hdc⟩ := exists_between hflow
    have hbound := F.rest_coefficient_eventually_le_filter
      (F.corner_eventually_stable ha hb hmargin) hd
    filter_upwards [hbound,F.epsilon_pos] with p hp he
    have hcoef : F.restCoefficientAt p<c := hp.trans_lt hdc
    have hh := (div_lt_iff₀ he).mp hcoef
    change 1-Momentum.momentumRestRate (F.tuning p).beta (F.tuning p).tau
      (F.tuning p).stepSize (F.tuning p).step_pos.ne' (F.epsilon p^2) 1<c*F.epsilon p at hh
    linarith
  · have hcle : c≤Flow.cF θ 2 := le_of_not_gt hflow
    have hcQ : c≤Flow.cQ θ 2 := hcle.trans (min_le_right _ _)
    have hcθ : c≤θ/3 := hcle.trans (min_le_left _ _)
    have hmin : min (Flow.cQ θ 2) (Corner.cDisc θ a b)<c :=
      (le_max_right _ _).trans_lt hc
    have hdisc : Corner.cDisc θ a b<c := by
      rcases min_lt_iff.mp hmin with h|h
      · exact False.elim ((not_lt_of_ge hcQ) h)
      · exact h
    obtain ⟨ξ,hξ,heq⟩ := Corner.cDisc_attained θ a b
    have hratio : Corner.ratio θ a b ξ<c := heq.trans_lt hdisc
    rcases Corner.discreteSet_iff.mp hξ with rfl|rfl|⟨K,hK,rfl⟩
    · rw [Corner.ratio_zero] at hratio
      exact False.elim ((not_lt_of_ge hcθ) hratio)
    · rw [Corner.ratio_two] at hratio
      exact F.corner_alternating_rest_lower ha hb hmargin hratio
    · obtain ⟨d,hd,hdc⟩ := exists_between (max_lt hc0 hratio)
      have hd0 : 0<d := (le_max_left _ _).trans_lt hd
      have hqd : Corner.ratio θ a b (Corner.rationalXi K)<d :=
        (le_max_right _ _).trans_lt hd
      have hw := F.corner_frequency_rest_witness ha hb hmargin hd0
        (hdc.trans_le hcθ) hK hqd
      filter_upwards [hw,F.epsilon_pos] with p hp he
      obtain ⟨dim,hactual,hrate⟩ := hp
      have hstrict : 1-c*F.epsilon p<1-d*F.epsilon p := by nlinarith
      exact hstrict.trans_le hrate

end
end nesterov.TwoStep.Scaling
