import nesterov.TwoStep.KnownTuningFinite
import nesterov.TwoStep.Bulk
import nesterov.TwoStep.BoundaryRates
import nesterov.Flow.Damping

/-! Corollary B: actual full-class and from-rest rates at the known tunings. -/
namespace nesterov.TwoStep.KnownTunings
noncomputable section
open Filter Set
open scoped Topology

private theorem epsilon_zero : Tendsto (fun ε : ℝ=>ε) (𝓝[>] (0:ℝ)) (𝓝 0) :=
  continuous_id.continuousWithinAt.tendsto

theorem standard_stable : ∀ᶠ ε in 𝓝[>] (0:ℝ),(standard.tuning ε).Stable (ε^2) 1 := by
  filter_upwards [standard_parameters,self_mem_nhdsWithin,
    epsilon_zero.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1))] with ε hp he he1
  have hε : 0<ε := he
  apply nesterov_stable _ (sq_pos_of_pos hε) (by nlinarith)
    (hp.2.1.trans hp.1.symm)
  rw [hp.2.2]
  norm_num

theorem quadraticOptimal_stable : ∀ᶠ ε in 𝓝[>] (0:ℝ),(quadraticOptimal.tuning ε).Stable (ε^2) 1 := by
  filter_upwards [quadraticOptimal_parameters,self_mem_nhdsWithin,
    epsilon_zero.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1))] with ε hp he he1
  have hε : 0<ε := he
  apply nesterov_stable _ (sq_pos_of_pos hε) (by nlinarith) (hp.2.1.trans hp.1.symm)
  rw [hp.2.2,mul_one]
  unfold quadraticOptimalStep
  apply (div_le_iff₀ (show 0<3+ε^2 by positivity)).mpr
  nlinarith [sq_nonneg ε]

theorem classOptimal_stable : ∀ᶠ ε in 𝓝[>] (0:ℝ),(classOptimal.tuning ε).Stable (ε^2) 1 := by
  filter_upwards [classOptimal_parameters,self_mem_nhdsWithin,
    epsilon_zero.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1))] with ε hp he he1
  have hε : 0<ε := he
  apply nesterov_stable _ (sq_pos_of_pos hε) (by nlinarith) (hp.2.1.trans hp.1.symm)
  rw [hp.2.2]
  norm_num

theorem overrelaxed_stable : ∀ᶠ ε in 𝓝[>] (0:ℝ),(overrelaxed.tuning ε).Stable (ε^2) 1 := by
  filter_upwards [overrelaxed_parameters,self_mem_nhdsWithin,
    epsilon_zero.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1))] with ε hp he he1
  have hε : 0<ε := he
  apply ((overrelaxed.tuning ε).stable_iff (sq_pos_of_pos hε) (by nlinarith : ε^2<1)).mpr
  rw [hp.1,hp.2.1,hp.2.2]
  have hb := (overrelaxed.tuning ε).beta_lt_one
  rw [hp.1] at hb
  nlinarith

theorem standard_constants : Flow.cQ 2 1=1 ∧ Flow.cF 2 1=2/3 := by
  norm_num [Flow.cQ,Flow.cF]

theorem quadraticOptimal_constants :
    Flow.cQ (4/Real.sqrt 3) (4/3)=2/Real.sqrt 3 ∧
      Flow.cF (4/Real.sqrt 3) (4/3)=4/(3*Real.sqrt 3) := by
  have hs : (Real.sqrt 3)^2=3 := Real.sq_sqrt (by norm_num)
  have hθsq : (4/Real.sqrt 3)^2=16/3 := by rw [div_pow,hs];norm_num
  have hq : Flow.cQ (4/Real.sqrt 3) (4/3)=(4/Real.sqrt 3)/2 :=
    Flow.cQ_eq_half (by nlinarith)
  have hp : 0<4/Real.sqrt 3 := by positivity
  constructor
  · rw [hq]
    ring
  · rw [Flow.cF,hq,min_eq_left (by linarith : (4/Real.sqrt 3)/3≤(4/Real.sqrt 3)/2)]
    ring

theorem classOptimal_constants :
    Flow.cQ (Real.sqrt 6) (4/3)=Real.sqrt (2/3) ∧
      Flow.cF (Real.sqrt 6) (4/3)=Real.sqrt (2/3) := by
  have hs₆ := Real.sq_sqrt (by norm_num : (0:ℝ)≤6)
  have hs₂ := Real.sq_sqrt (by norm_num : (0:ℝ)≤2/3)
  have heq : Real.sqrt 6=3*Real.sqrt (2/3) := by
    nlinarith [Real.sqrt_nonneg (6:ℝ),Real.sqrt_nonneg (2/3:ℝ)]
  rw [heq]
  constructor
  · simpa only [show (4/3:ℝ)/2=2/3 by norm_num] using
      (Flow.cQ_at_nonlinear_optimal (by norm_num : (0:ℝ)<4/3))
  · simpa only [show (4/3:ℝ)/2=2/3 by norm_num] using
      (Flow.cF_at_nonlinear_optimal (by norm_num : (0:ℝ)<4/3))

theorem standard_rates :
    Tendsto standard.fullCoefficient (𝓝[>] (0:ℝ)) (𝓝 (2/3)) ∧
      Tendsto standard.restCoefficient (𝓝[>] (0:ℝ)) (𝓝 (2/3)) := by
  simpa only [standard_constants.2] using
    standard.bulk_coefficients_tendsto rfl standard_stable (by norm_num) (by norm_num)

theorem overrelaxed_rates :
    Tendsto overrelaxed.fullCoefficient (𝓝[>] (0:ℝ)) (𝓝 (2/3)) ∧
      Tendsto overrelaxed.restCoefficient (𝓝[>] (0:ℝ)) (𝓝 (2/3)) := by
  simpa only [standard_constants.2] using
    overrelaxed.bulk_coefficients_tendsto rfl overrelaxed_stable (by norm_num) (by norm_num)

theorem quadraticOptimal_margin_tendsto :
    Tendsto quadraticOptimal.stabilityMargin (𝓝[>] (0:ℝ)) (𝓝 (32/(3*Real.sqrt 3))) := by
  have ht := ((epsilon_zero.const_mul 4).add (quadraticOptimal_theta_tendsto.const_mul 8)).div
    ((tendsto_const_nhds (x:=(3:ℝ))).add (epsilon_zero.pow 2)) (by norm_num : (3+0^2:ℝ)≠0)
  have hv : (4*0+8*(4/Real.sqrt 3))/(3+0^2)=32/(3*Real.sqrt 3) := by ring
  rw [hv] at ht
  apply ht.congr'
  filter_upwards [quadraticOptimal_parameters,self_mem_nhdsWithin] with ε hp he
  have hε : 0<ε := he
  unfold Scaling.stabilityMargin
  rw [hp.2.1,hp.2.2]
  change _=(4-quadraticOptimalStep ε*(1+2*quadraticOptimalBeta ε))/ε
  dsimp only [Pi.div_apply]
  unfold quadraticOptimalStep
  field_simp [hε.ne',show 3+ε^2≠0 by positivity]
  ring

theorem classOptimal_margin_tendsto :
    Tendsto classOptimal.stabilityMargin (𝓝[>] (0:ℝ)) (𝓝 (8*Real.sqrt 6/3)) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [classOptimal_parameters,self_mem_nhdsWithin] with ε hp he
  have hε : 0<ε := he
  unfold Scaling.stabilityMargin
  rw [hp.2.1,hp.2.2]
  change (8*Real.sqrt 6/3:ℝ)=(4-(4/3)*(1+2*classOptimalBeta ε))/ε
  unfold classOptimalBeta
  field_simp [hε.ne']
  ring

theorem quadraticOptimal_rates :
    Tendsto quadraticOptimal.fullCoefficient (𝓝[>] (0:ℝ)) (𝓝 (4/(3*Real.sqrt 3))) ∧
      Tendsto quadraticOptimal.restCoefficient (𝓝[>] (0:ℝ)) (𝓝 (4/(3*Real.sqrt 3))) := by
  have hθ : 0<4/Real.sqrt 3 := by positivity
  have hs : 2*(4/Real.sqrt 3)<32/(3*Real.sqrt 3) := by
    have hp : 0<(Real.sqrt 3)⁻¹ := inv_pos.mpr (Real.sqrt_pos.mpr (by norm_num))
    field_simp
    nlinarith
  have hcpi : alternatingConstant (4/Real.sqrt 3) 1 (32/(3*Real.sqrt 3))=2/Real.sqrt 3 := by
    unfold alternatingConstant
    ring
  have ht := quadraticOptimal.boundary_coefficients_tendsto rfl quadraticOptimal_stable
    (by norm_num) (by norm_num) quadraticOptimal_margin_tendsto hs
  have hmin : 4/(3*Real.sqrt 3)≤2/Real.sqrt 3 := by
    calc
      4/(3*Real.sqrt 3)=(4/3)/Real.sqrt 3 := by ring
      _≤_ := div_le_div_of_nonneg_right (by norm_num : (4/3:ℝ)≤2) (Real.sqrt_nonneg _)
  rw [quadraticOptimal_constants.2,hcpi,min_eq_left hmin] at ht
  exact ht

theorem classOptimal_rates :
    Tendsto classOptimal.fullCoefficient (𝓝[>] (0:ℝ)) (𝓝 (Real.sqrt (2/3))) ∧
      Tendsto classOptimal.restCoefficient (𝓝[>] (0:ℝ)) (𝓝 (Real.sqrt (2/3))) := by
  have hp : 0<Real.sqrt 6 := Real.sqrt_pos.mpr (by norm_num)
  have hs : 2*Real.sqrt 6<8*Real.sqrt 6/3 := by linarith
  have hcpi : alternatingConstant (Real.sqrt 6) 1 (8*Real.sqrt 6/3)=Real.sqrt 6/2 := by
    unfold alternatingConstant
    ring
  have hmin : Real.sqrt (2/3)≤Real.sqrt 6/2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤2/3),Real.sq_sqrt (by norm_num : (0:ℝ)≤6),
      Real.sqrt_nonneg (2/3:ℝ)]
  have ht := classOptimal.boundary_coefficients_tendsto rfl classOptimal_stable
    (by norm_num) (by norm_num) classOptimal_margin_tendsto hs
  simpa only [classOptimal_constants.2,hcpi,min_eq_left hmin] using ht

end
end nesterov.TwoStep.KnownTunings
