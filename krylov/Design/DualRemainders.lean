import krylov.Design.HyperbolicDual

/-!
Article: main_krylov, apC:lem:poisson, precise exponentially small dual tails.
Use: prove strict positivity and both exact leading exponential coefficients
for the genuine dual series displayed on the right of the Poisson formulas.
The identities equating these dual tails with the primary-series remainders
are separate Fourier/Poisson statements and are not assumed here.
Source: the proved Lambert series bounds and the inverse-spacing limit.
-/

namespace krylov.Design
noncomputable section
open Real Filter jacobi.Young
open scoped Topology

/-- The actual first dual-series tail in the secant Poisson formula.
Article: main_krylov, apC:lem:poisson. -/
def sechDualTail (θ : ℝ) : ℝ := π / θ * sampledSech (π ^ 2 / θ)

/-- The actual second dual-series tail in the squared-secant Poisson formula.
Article: main_krylov, apC:lem:poisson. -/
def sechSquaredDualTail (θ : ℝ) : ℝ := 2 * π ^ 2 / θ ^ 2 * sampledWeightedCsch (π ^ 2 / θ)

/-- Both actual hyperbolic dual sums are strictly positive at every positive spacing.
Article: main_krylov, apC:lem:poisson, positivity of the two remainders. -/
theorem hyperbolic_dual_sums_pos {A : ℝ} (hA : 0 < A) :
    0 < sampledSech A ∧ 0 < sampledWeightedCsch A := by
  have hq := exp_pos (-A)
  have hq1 : exp (-A) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hq2 : exp (-A) ^ 2 < 1 := pow_lt_one₀ hq.le hq1 (by norm_num)
  rw [sampledSech_eq_lambert, sampledWeightedCsch_eq_lambert hA]
  constructor
  · exact mul_pos (by norm_num) ((div_pos hq (by positivity)).trans_le
      (sechLambert_bounds hq.le hq1).1)
  · exact mul_pos (by norm_num) ((div_pos hq (sub_pos.mpr hq2)).trans_le
      (cschLambert_bounds hq.le hq1).1)

/-- Both actual dual tails are strictly positive at every positive original spacing.
Article: main_krylov, apC:lem:poisson. -/
theorem dual_tails_pos {θ : ℝ} (hθ : 0 < θ) : 0 < sechDualTail θ ∧ 0 < sechSquaredDualTail θ := by
  have hp := hyperbolic_dual_sums_pos (div_pos (sq_pos_of_pos Real.pi_pos) hθ)
  exact ⟨mul_pos (div_pos Real.pi_pos hθ) hp.1,
    mul_pos (div_pos (by positivity) (sq_pos_of_pos hθ)) hp.2⟩

/-- The actual first dual tail is asymptotic to (2*pi/theta)*exp(-pi^2/theta).
Article: main_krylov, apC:lem:poisson, the exact first exponential coefficient. -/
theorem sechDualTail_exponential_asymptotic :
    Tendsto (fun θ : ℝ => sechDualTail θ / (2 * π / θ * exp (-(π ^ 2 / θ))))
      (𝓝[>] 0) (𝓝 1) := by
  have hA : Tendsto (fun θ : ℝ => π ^ 2 / θ) (𝓝[>] 0) atTop := by
    simpa only [div_eq_mul_inv] using
      Filter.Tendsto.const_mul_atTop (sq_pos_of_pos Real.pi_pos) tendsto_inv_nhdsGT_zero
  have h := sampledSech_exponential_asymptotic.comp hA
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with θ hθ
  have hθpos : 0 < θ := hθ
  simp only [Function.comp_def, sechDualTail]
  field_simp [hθpos.ne', Real.pi_ne_zero]

/-- The actual second dual tail is asymptotic to (4*pi^2/theta^2)*exp(-pi^2/theta).
Article: main_krylov, apC:lem:poisson, the exact second exponential coefficient. -/
theorem sechSquaredDualTail_exponential_asymptotic :
    Tendsto (fun θ : ℝ => sechSquaredDualTail θ / (4 * π ^ 2 / θ ^ 2 * exp (-(π ^ 2 / θ))))
      (𝓝[>] 0) (𝓝 1) := by
  have hA : Tendsto (fun θ : ℝ => π ^ 2 / θ) (𝓝[>] 0) atTop := by
    simpa only [div_eq_mul_inv] using
      Filter.Tendsto.const_mul_atTop (sq_pos_of_pos Real.pi_pos) tendsto_inv_nhdsGT_zero
  have h := sampledWeightedCsch_exponential_asymptotic.comp hA
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with θ hθ
  have hθpos : 0 < θ := hθ
  simp only [Function.comp_def, sechSquaredDualTail]
  field_simp [hθpos.ne', Real.pi_ne_zero]
  norm_num

end
end krylov.Design
