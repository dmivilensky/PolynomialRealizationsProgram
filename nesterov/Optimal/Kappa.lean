import nesterov.Optimal.Source
import nesterov.Slow.Kappa

/-! Literal condition-number forms of both directions of the optimal-tuning theorem. -/
namespace nesterov.TwoStep
noncomputable section
open Filter
open scoped Topology

def tuningFullKappaCoefficient (q : ℝ→Momentum.Tuning) (κ : ℝ) : ℝ :=
  Real.sqrt κ*(1-Momentum.momentumRate (q κ).beta (q κ).tau (q κ).stepSize
    (q κ).step_pos.ne' (1/κ) 1)

def tuningRestKappaCoefficient (q : ℝ→Momentum.Tuning) (κ : ℝ) : ℝ :=
  Real.sqrt κ*(1-Momentum.momentumRestRate (q κ).beta (q κ).tau (q κ).stepSize
    (q κ).step_pos.ne' (1/κ) 1)

theorem tuningFullKappaCoefficient_eventually_eq (q : ℝ→Momentum.Tuning) :
    tuningFullKappaCoefficient q=ᶠ[atTop]
      (fun κ=>tuningFullCoefficient (Slow.epsilon κ) (q κ)) := by
  filter_upwards [eventually_gt_atTop (0:ℝ)] with κ hκ
  let R : ℝ→ℝ := fun μ=>Momentum.momentumRate (q κ).beta (q κ).tau (q κ).stepSize
    (q κ).step_pos.ne' μ 1
  change Real.sqrt κ*(1-R (1/κ))=(1-R (Slow.epsilon κ^2))/Slow.epsilon κ
  rw [Slow.epsilon_sq hκ.le]
  exact (Slow.coefficient_kappa hκ).symm

theorem tuningRestKappaCoefficient_eventually_eq (q : ℝ→Momentum.Tuning) :
    tuningRestKappaCoefficient q=ᶠ[atTop]
      (fun κ=>tuningRestCoefficient (Slow.epsilon κ) (q κ)) := by
  filter_upwards [eventually_gt_atTop (0:ℝ)] with κ hκ
  let R : ℝ→ℝ := fun μ=>Momentum.momentumRestRate (q κ).beta (q κ).tau (q κ).stepSize
    (q κ).step_pos.ne' μ 1
  change Real.sqrt κ*(1-R (1/κ))=(1-R (Slow.epsilon κ^2))/Slow.epsilon κ
  rw [Slow.epsilon_sq hκ.le]
  exact (Slow.coefficient_kappa hκ).symm

private theorem kappa_stability_to_epsilon (q : ℝ→Momentum.Tuning)
    (hs : ∀ᶠ κ in atTop,(q κ).Stable (1/κ) 1) :
    ∀ᶠ κ in atTop,(q κ).Stable (Slow.epsilon κ^2) 1 := by
  filter_upwards [hs,eventually_gt_atTop (0:ℝ)] with κ hκ hp
  simpa only [Slow.epsilon_sq hp.le] using hκ

theorem optimal_tuning_kappa_iff (q : ℝ→Momentum.Tuning)
    (hs : ∀ᶠ κ in atTop,(q κ).Stable (1/κ) 1) :
    Tendsto (tuningFullKappaCoefficient q) atTop (𝓝 1) ↔
      Tendsto (fun κ=>parameterTriple (Slow.epsilon κ) (q κ)) atTop (𝓝 (3,(2,1/2))) ∧
        Tendsto (fun κ=>tuningCornerLag (Slow.epsilon κ) (q κ)) atTop (𝓝 1) := by
  have h := optimal_tuning_family_iff Slow.epsilon_tendsto (kappa_stability_to_epsilon q hs)
  constructor
  · intro hf
    exact h.mp (hf.congr' (tuningFullKappaCoefficient_eventually_eq q))
  · intro hr
    exact (h.mpr hr).congr' (tuningFullKappaCoefficient_eventually_eq q).symm

theorem optimal_tuning_kappa_ratio_iff (q : ℝ→Momentum.Tuning)
    (hs : ∀ᶠ κ in atTop,(q κ).Stable (1/κ) 1) :
    Tendsto (tuningFullKappaCoefficient q) atTop (𝓝 1) ↔
      Tendsto (fun κ=>parameterTriple (Slow.epsilon κ) (q κ)) atTop (𝓝 (3,(2,1/2))) ∧
        (7:EReal)≤liminf (fun κ=>(tuningCornerMargin (Slow.epsilon κ) (q κ):EReal)) atTop ∧
          Tendsto (fun κ=>tuningCornerCriterionRatio (Slow.epsilon κ) (q κ)) atTop (𝓝 0) := by
  have h := optimal_tuning_family_ratio_iff Slow.epsilon_tendsto (kappa_stability_to_epsilon q hs)
  constructor
  · intro hf
    exact h.mp (hf.congr' (tuningFullKappaCoefficient_eventually_eq q))
  · intro hr
    exact (h.mpr hr).congr' (tuningFullKappaCoefficient_eventually_eq q).symm

theorem optimal_tuning_kappa_rest_limit (q : ℝ→Momentum.Tuning)
    (hs : ∀ᶠ κ in atTop,(q κ).Stable (1/κ) 1)
    (hf : Tendsto (tuningFullKappaCoefficient q) atTop (𝓝 1)) :
    Tendsto (tuningRestKappaCoefficient q) atTop (𝓝 1) := by
  have h := optimal_tuning_rest_limit Slow.epsilon_tendsto (kappa_stability_to_epsilon q hs)
    (hf.congr' (tuningFullKappaCoefficient_eventually_eq q))
  exact h.congr' (tuningRestKappaCoefficient_eventually_eq q).symm

end
end nesterov.TwoStep
