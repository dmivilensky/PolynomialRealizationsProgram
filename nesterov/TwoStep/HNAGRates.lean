import nesterov.TwoStep.HNAGGerms
import nesterov.Momentum.HNAG
import nesterov.Corner.Consequences
import nesterov.Corner.Kappa
import nesterov.TwoStep.KnownMethodBridges
import nesterov.Rates.FirstOrder

/-! Sharp uniform and quadratic HNAG++ constants from the existing corner theorem. -/
namespace nesterov.TwoStep.HNAG
noncomputable section
open Filter Set
open scoped Topology

theorem physical_step {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : E→E) {ε : ℝ} (hε : 0<ε) (p : E × E) :
    Momentum.Correction.step g (beta ε) (tau ε) (step ε) p=
      (p.2,p.2+(beta ε) • (p.2-p.1)-
        ((3+Real.sqrt 2*ε)/(1+Real.sqrt 2*ε)^2) • g p.2+
        (1/(1+Real.sqrt 2*ε)^2) • g p.1) := by
  have h1 : step ε*(1+tau ε)=(3+Real.sqrt 2*ε)/(1+Real.sqrt 2*ε)^2 := by
    unfold step tau
    field_simp [show 1+Real.sqrt 2*ε≠0 by positivity,
      show 2+Real.sqrt 2*ε≠0 by positivity]
    ring
  have h2 : step ε*tau ε=1/(1+Real.sqrt 2*ε)^2 := by
    unfold step tau
    field_simp [show 1+Real.sqrt 2*ε≠0 by positivity,
      show 2+Real.sqrt 2*ε≠0 by positivity]
  unfold Momentum.Correction.step
  rw [h1,h2]

theorem uniform_coefficients :
    Tendsto family.fullCoefficientAt (𝓝[>] (0:ℝ)) (𝓝 (2*Real.sqrt 2/3)) ∧
      Tendsto family.restCoefficientAt (𝓝[>] (0:ℝ)) (𝓝 (2*Real.sqrt 2/3)) := by
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
  have hr := Real.sqrt_nonneg (2:ℝ)
  exact family.corner_flow_region corner_coordinates.1 corner_coordinates.2
    (by nlinarith : 2*Real.sqrt 2≤3) (by nlinarith) (by nlinarith)

theorem quadratic_coefficient :
    Tendsto (fun ε=>(1-family.rate ε)/family.epsilon ε)
      (𝓝[>] (0:ℝ)) (𝓝 (Real.sqrt 2)) := by
  have hr : 0<Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hstable := family.corner_eventually_stable corner_coordinates.1 corner_coordinates.2
    (by linarith : 2*Real.sqrt 2<2*(Real.sqrt 2/4)+3*Real.sqrt 2)
  have h := family.quadratic_boundary_coefficient_tendsto (by norm_num : (1/2:ℝ)≤1/2)
    (by norm_num : (2:ℝ)*(1+2*(1/2))=4) hstable
    (family.corner_margin_tendsto corner_coordinates.1 corner_coordinates.2)
  have hp : alternatingConstant (2*Real.sqrt 2) (1/2)
      (4*(Real.sqrt 2/4)+2*(3*Real.sqrt 2))=3*Real.sqrt 2 := by
    unfold alternatingConstant
    norm_num
    ring
  rw [Flow.cQ_critical (by norm_num : (0:ℝ)≤2),hp,min_eq_left (by linarith)] at h
  exact h

theorem kappa_rates :
    Tendsto family.fullKappaCoefficient atTop (𝓝 (2*Real.sqrt 2/3)) ∧
      Tendsto family.restKappaCoefficient atTop (𝓝 (2*Real.sqrt 2/3)) ∧
        Tendsto family.quadraticKappaCoefficient atTop (𝓝 (Real.sqrt 2)) := by
  have h := family.coefficientsAt_kappa_transport rfl uniform_coefficients.1 uniform_coefficients.2
  exact ⟨h.1,h.2,family.quadraticAt_kappa_transport rfl quadratic_coefficient⟩

theorem physical_quadratic_kappa_rate :
    Tendsto (fun κ : ℝ=>Real.sqrt κ*(1-Quadratic.quadraticRate (1/κ) 1
      (beta (Slow.epsilon κ)) (tau (Slow.epsilon κ)) (step (Slow.epsilon κ))))
      atTop (𝓝 (Real.sqrt 2)) := by
  apply kappa_rates.2.2.congr'
  filter_upwards [Slow.epsilon_tendsto.eventually parameters] with κ hp
  simp only [Scaling.quadraticKappaCoefficient,hp.1,hp.2.1,hp.2.2]

/-- The actual gradient-correction executor, with arbitrary initial physical memories. -/
theorem physical_correction_coefficient :
    Tendsto (fun ε : ℝ=>(1-Momentum.Correction.rate (beta ε) (tau ε) (step ε) (ε^2) 1)/ε)
      (𝓝[>] (0:ℝ)) (𝓝 (2*Real.sqrt 2/3)) := by
  apply uniform_coefficients.1.congr'
  filter_upwards [family.correction_rate_eventually_eq,parameters] with ε hr hp
  change Momentum.Correction.rate _ _ _ (ε^2) 1=Momentum.momentumRate _ _ _ _ (ε^2) 1 at hr
  change (1-Momentum.momentumRate (family.tuning ε).beta (family.tuning ε).tau
    (family.tuning ε).stepSize (family.tuning ε).step_pos.ne' (ε^2) 1)/ε=_
  simpa only [hp.1,hp.2.1,hp.2.2] using congrArg (fun r : ℝ=>(1-r)/ε) hr.symm

theorem physical_correction_kappa_rate :
    Tendsto (fun κ : ℝ=>Real.sqrt κ*(1-Momentum.Correction.rate
      (beta (Slow.epsilon κ)) (tau (Slow.epsilon κ)) (step (Slow.epsilon κ)) (1/κ) 1))
      atTop (𝓝 (2*Real.sqrt 2/3)) := by
  apply (coefficient_tendsto_kappa physical_correction_coefficient).congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with κ hκ
  simp only [Slow.epsilon_sq hκ.le]

theorem physical_squared_kappa_rate :
    Tendsto (fun κ : ℝ=>Real.sqrt κ*(1-(Momentum.Correction.rate
      (beta (Slow.epsilon κ)) (tau (Slow.epsilon κ)) (step (Slow.epsilon κ)) (1/κ) 1)^2))
      atTop (𝓝 (4*Real.sqrt 2/3)) := by
  have he : Tendsto (fun ε : ℝ=>ε) (𝓝[>] (0:ℝ)) (𝓝 0) :=
    continuous_id.continuousWithinAt.tendsto
  have hn : ∀ᶠ ε in 𝓝[>] (0:ℝ),ε≠0 := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (show 0<ε from hε).ne'
  have h := Rates.squared_coefficient_tendsto he hn physical_correction_coefficient
  rw [show 2*(2*Real.sqrt 2/3)=4*Real.sqrt 2/3 by ring] at h
  apply (coefficient_tendsto_kappa h).congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with κ hκ
  simp only [Slow.epsilon_sq hκ.le]

end
end nesterov.TwoStep.HNAG
