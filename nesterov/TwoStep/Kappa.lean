import nesterov.TwoStep.Bulk
import nesterov.Slow.Kappa

/-! Literal condition-number versions of the accelerated rate limits. -/
namespace nesterov.TwoStep
noncomputable section
open Filter
open scoped Topology

 theorem coefficient_tendsto_kappa {R : ℝ→ℝ} {c : ℝ}
    (h : Tendsto (fun ε=>(1-R ε)/ε) (𝓝[>] (0:ℝ)) (𝓝 c)) :
    Tendsto (fun κ=>Real.sqrt κ*(1-R (Slow.epsilon κ))) atTop (𝓝 c) := by
  apply (h.comp Slow.epsilon_tendsto).congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with κ hκ
  exact Slow.coefficient_kappa hκ

namespace Scaling
variable {θ y τ : ℝ} (F : Scaling ℝ (𝓝[>] (0:ℝ)) θ y τ)

def fullKappaCoefficient (κ : ℝ) : ℝ :=
  Real.sqrt κ*(1-Momentum.momentumRate (F.tuning (Slow.epsilon κ)).beta
    (F.tuning (Slow.epsilon κ)).tau (F.tuning (Slow.epsilon κ)).stepSize
    (F.tuning (Slow.epsilon κ)).step_pos.ne' (1/κ) 1)

def restKappaCoefficient (κ : ℝ) : ℝ :=
  Real.sqrt κ*(1-Momentum.momentumRestRate (F.tuning (Slow.epsilon κ)).beta
    (F.tuning (Slow.epsilon κ)).tau (F.tuning (Slow.epsilon κ)).stepSize
    (F.tuning (Slow.epsilon κ)).step_pos.ne' (1/κ) 1)

 theorem full_kappa_transport {c : ℝ} (h : Tendsto F.fullCoefficient (𝓝[>] (0:ℝ)) (𝓝 c)) :
    Tendsto F.fullKappaCoefficient atTop (𝓝 c) := by
  apply (coefficient_tendsto_kappa h).congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with κ hκ
  simp only [fullKappaCoefficient,Slow.epsilon_sq hκ.le]

 theorem rest_kappa_transport {c : ℝ} (h : Tendsto F.restCoefficient (𝓝[>] (0:ℝ)) (𝓝 c)) :
    Tendsto F.restKappaCoefficient atTop (𝓝 c) := by
  apply (coefficient_tendsto_kappa h).congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with κ hκ
  simp only [restKappaCoefficient,Slow.epsilon_sq hκ.le]

 theorem bulk_kappa_constants (he : F.epsilon=id)
    (hs : ∀ᶠ ε in 𝓝[>] (0:ℝ),(F.tuning ε).Stable (ε^2) 1)
    (hτ : 1/2<τ) (hmargin : y*(1+2*τ)<4) :
    Tendsto F.fullKappaCoefficient atTop (𝓝 (Flow.cF θ y)) ∧
      Tendsto F.restKappaCoefficient atTop (𝓝 (Flow.cF θ y)) := by
  have hh := F.bulk_coefficients_tendsto he hs hτ hmargin
  exact ⟨F.full_kappa_transport hh.1,F.rest_kappa_transport hh.2⟩

end Scaling
end
end nesterov.TwoStep
