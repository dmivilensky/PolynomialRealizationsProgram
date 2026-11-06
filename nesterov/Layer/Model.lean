import nesterov.TwoStep.ScaledCoefficientsLimits
import nesterov.Layer.Constants

/-! The moving deficit at the epsilon^(1/2) half-step scale. -/
namespace nesterov.TwoStep.Scaling
noncomputable section
open Filter
open scoped Topology
variable {A : Type*} {l : Filter A} {θ y τ : ℝ} (F : Scaling A l θ y τ)

def layerDeficit (a : A) : ℝ := (1/2-(F.tuning a).tau)/Real.sqrt (F.epsilon a)

theorem sqrt_epsilon_tendsto :
    Tendsto (fun a => Real.sqrt (F.epsilon a)) l (𝓝 0) := by
  simpa only [Real.sqrt_zero] using F.epsilon_zero.sqrt

theorem layerDeficit_exact : ∀ᶠ a in l,
    2*(F.tuning a).tau-1= -2*F.layerDeficit a*Real.sqrt (F.epsilon a) := by
  filter_upwards [F.epsilon_pos] with a ha
  have hs := Real.sqrt_pos.mpr ha
  unfold layerDeficit
  field_simp
  ring

theorem positive_deficit_tendsto {B : ℝ}
    (hB : Tendsto F.layerDeficit l (𝓝 B)) :
    Tendsto (fun a => max (F.layerDeficit a) 0) l (𝓝 (max B 0)) :=
  hB.max tendsto_const_nhds

theorem positive_deficit_tendsto_of_atBot
    (hB : Tendsto F.layerDeficit l atBot) :
    Tendsto (fun a => max (F.layerDeficit a) 0) l (𝓝 0) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [hB.eventually_le_atBot 0] with a ha
  exact (max_eq_right ha).symm

end
end nesterov.TwoStep.Scaling
