import nesterov.TwoStep.KnownTuningRates
import nesterov.TwoStep.KnownMethodBridges
import nesterov.TwoStep.Kappa
import nesterov.Rates.FirstOrder

/-! The known tunings in the literal condition-number variable, including
the squared-distance factor of standard Nesterov. -/
namespace nesterov.TwoStep.KnownTunings
noncomputable section
open Filter
open scoped Topology

theorem standard_kappa_rates :
    Tendsto standard.fullKappaCoefficient atTop (𝓝 (2/3)) ∧
      Tendsto standard.restKappaCoefficient atTop (𝓝 (2/3)) :=
  ⟨standard.full_kappa_transport standard_rates.1,
    standard.rest_kappa_transport standard_rates.2⟩

theorem quadraticOptimal_kappa_rates :
    Tendsto quadraticOptimal.fullKappaCoefficient atTop (𝓝 (4/(3*Real.sqrt 3))) ∧
      Tendsto quadraticOptimal.restKappaCoefficient atTop (𝓝 (4/(3*Real.sqrt 3))) :=
  ⟨quadraticOptimal.full_kappa_transport quadraticOptimal_rates.1,
    quadraticOptimal.rest_kappa_transport quadraticOptimal_rates.2⟩

theorem classOptimal_kappa_rates :
    Tendsto classOptimal.fullKappaCoefficient atTop (𝓝 (Real.sqrt (2/3))) ∧
      Tendsto classOptimal.restKappaCoefficient atTop (𝓝 (Real.sqrt (2/3))) :=
  ⟨classOptimal.full_kappa_transport classOptimal_rates.1,
    classOptimal.rest_kappa_transport classOptimal_rates.2⟩

theorem classOptimal_literal_kappa_rates :
    Tendsto (fun κ => Real.sqrt κ*(1-Momentum.momentumRate
      (1-Real.sqrt (6/κ)) (1-Real.sqrt (6/κ)) (4/3) (by norm_num) (1/κ) 1))
      atTop (𝓝 (Real.sqrt (2/3))) ∧
    Tendsto (fun κ => Real.sqrt κ*(1-Momentum.momentumRestRate
      (1-Real.sqrt (6/κ)) (1-Real.sqrt (6/κ)) (4/3) (by norm_num) (1/κ) 1))
      atTop (𝓝 (Real.sqrt (2/3))) := by
  have hparam : ∀ᶠ κ in atTop,
      (classOptimal.tuning (Slow.epsilon κ)).beta=1-Real.sqrt (6/κ) ∧
      (classOptimal.tuning (Slow.epsilon κ)).tau=1-Real.sqrt (6/κ) ∧
      (classOptimal.tuning (Slow.epsilon κ)).stepSize=4/3 := by
    filter_upwards [Slow.epsilon_tendsto.eventually classOptimal_parameters] with κ hp
    have hb : classOptimalBeta (Slow.epsilon κ)=1-Real.sqrt (6/κ) := by
      rw [Real.sqrt_div (by norm_num : (0:ℝ)≤6)]
      simp only [classOptimalBeta,Slow.epsilon,mul_one_div]
    exact ⟨hp.1.trans hb,hp.2.1.trans hb,hp.2.2⟩
  constructor
  · apply classOptimal_kappa_rates.1.congr'
    filter_upwards [hparam] with κ hp
    simp only [Scaling.fullKappaCoefficient,hp.1,hp.2.1,hp.2.2]
  · apply classOptimal_kappa_rates.2.congr'
    filter_upwards [hparam] with κ hp
    simp only [Scaling.restKappaCoefficient,hp.1,hp.2.1,hp.2.2]

theorem overrelaxed_kappa_rates :
    Tendsto overrelaxed.fullKappaCoefficient atTop (𝓝 (2/3)) ∧
      Tendsto overrelaxed.restKappaCoefficient atTop (𝓝 (2/3)) :=
  ⟨overrelaxed.full_kappa_transport overrelaxed_rates.1,
    overrelaxed.rest_kappa_transport overrelaxed_rates.2⟩

theorem overrelaxed_physical_kappa_rate :
    Tendsto (fun κ => Real.sqrt κ*(1-Momentum.Correction.rate
      (overrelaxedStep (Slow.epsilon κ)) 1 (overrelaxedStep (Slow.epsilon κ)) (1/κ) 1))
      atTop (𝓝 (2/3)) := by
  apply (coefficient_tendsto_kappa overrelaxed_physical_rate).congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with κ hκ
  simp only [Slow.epsilon_sq hκ.le]

theorem standard_squared_rate :
    Tendsto (fun ε =>
      (1-(Momentum.momentumRate (standard.tuning ε).beta (standard.tuning ε).tau
        (standard.tuning ε).stepSize (standard.tuning ε).step_pos.ne' (ε^2) 1)^2)/ε)
      (𝓝[>] (0:ℝ)) (𝓝 (4/3)) := by
  have he : Tendsto (fun ε : ℝ => ε) (𝓝[>] (0:ℝ)) (𝓝 0) :=
    continuous_id.continuousWithinAt.tendsto
  have hn : ∀ᶠ ε in 𝓝[>] (0:ℝ), ε ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (show 0<ε from hε).ne'
  simpa only [show (2:ℝ)*(2/3)=4/3 by norm_num] using
    Rates.squared_coefficient_tendsto he hn standard_rates.1

theorem standard_squared_kappa_rate :
    Tendsto (fun κ => Real.sqrt κ*
      (1-(Momentum.momentumRate (standard.tuning (Slow.epsilon κ)).beta
        (standard.tuning (Slow.epsilon κ)).tau
        (standard.tuning (Slow.epsilon κ)).stepSize
        (standard.tuning (Slow.epsilon κ)).step_pos.ne' (1/κ) 1)^2))
      atTop (𝓝 (4/3)) := by
  apply (coefficient_tendsto_kappa standard_squared_rate).congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with κ hκ
  simp only [Slow.epsilon_sq hκ.le]

end
end nesterov.TwoStep.KnownTunings
