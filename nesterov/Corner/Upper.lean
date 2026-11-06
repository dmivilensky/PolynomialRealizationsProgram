import nesterov.Corner.Expansion
import nesterov.Corner.Algebra

/-! The source corner upper bound is an actual lag-one rate certificate. -/
namespace nesterov.TwoStep.Scaling
noncomputable section
open Filter Set
open scoped Topology
variable {A : Type*} {l : Filter A} {θ : ℝ} (F : Scaling A l θ 2 (1/2))

theorem corner_tail_eventually_positive {a b c : ℝ}
    (ha : Tendsto F.cornerA l (𝓝 a)) (hb : Tendsto F.cornerB l (𝓝 b))
    (hc : c<Corner.cLag θ a b) :
    ∀ᶠ p in l,∀ ξ∈Icc (0:ℝ) 2,
      0<scaledTail (F.epsilon p) c (F.thetaAt p) (F.tuning p).stepSize (F.tuning p).tau ξ := by
  have hu := Metric.tendstoUniformlyOn_iff.mp (F.corner_tail_uniform c ha hb (isCompact_Icc (a:=(0:ℝ)) (b:=2)))
  have hm : 0<2*(Corner.cLag θ a b-c) := by linarith
  filter_upwards [F.epsilon_pos,hu _ hm] with p hp he ξ hξ
  have hclose := he ξ hξ
  rw [Real.dist_eq] at hclose
  have hlow := Corner.uniform_tail_margin (θ:=θ) (a:=a) (b:=b) hξ hc
  have hpos : 0<scaledTail (F.epsilon p) c (F.thetaAt p) (F.tuning p).stepSize
      (F.tuning p).tau ξ/F.epsilon p := by
    rcases abs_lt.mp hclose with ⟨hleft,hright⟩
    linarith
  exact (div_pos_iff_of_pos_right hp).mp hpos

theorem corner_lagOne_upper {a b c : ℝ}
    (ha : Tendsto F.cornerA l (𝓝 a)) (hb : Tendsto F.cornerB l (𝓝 b))
    (hc0 : 0<c) (hc : c<min (Flow.cQ θ 2) (Corner.cLag θ a b)) :
    ∀ᶠ p in l,Momentum.momentumRate (F.tuning p).beta (F.tuning p).tau
      (F.tuning p).stepSize (F.tuning p).step_pos.ne' (F.epsilon p^2) 1<1-c*F.epsilon p :=
  (F.lag_scaled hc0 (hc.trans_le (min_le_left _ _))
    (F.corner_tail_eventually_positive ha hb (hc.trans_le (min_le_right _ _)))).mono
      fun _ h=>h.2.2

end
end nesterov.TwoStep.Scaling
