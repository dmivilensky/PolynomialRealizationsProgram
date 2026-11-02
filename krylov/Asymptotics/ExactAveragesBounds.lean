import krylov.Asymptotics.ExactAveragesIntegrals
import krylov.Asymptotics.AveragingBounds

/-!
Article: main_krylov, apC:lem:step, the full exact averaged comparisons.
Use: integrate the sharp endpoint control bounds while retaining the
reciprocal-affine factor exactly.  The code's impulseAverage is reciprocal
to the source A-I, so source ratios are the products proved below.
Source: the true drift/impulse integrals, FTC log averages and log-Lipschitz control.
-/

namespace krylov.Asymptotics.DiscreteString
noncomputable section
open Real Set MeasureTheory ExactAverages
open krylov.Strings krylov.ContinuumControl
open scoped Topology
variable {N : ℕ} (S : krylov.Strings.DiscreteString N)
variable {γ : ℝ} {σ : ℝ → ℝ} (hgraph : ∀ r ≥ 1, FeedbackGraphAt γ σ r)
include hgraph

/-- Integrating a drift control upper bound retains the full true
logarithmic average instead of replacing the affine position by an endpoint. -/
theorem driftAverage_ge_log_of_tau_bound {j : ℕ} (hj : j < N) {T : ℝ} (_hT : 0 < T)
    (hbound : ∀ u ∈ Icc 0 (S.gap j), sqrt (σ (driftRatio S j u)) ≤ T) :
    (driftLog S j / S.gap j) / T ≤ driftAverage S σ j := by
  obtain ⟨hφ, hp, _, _⟩ := S.state_bounds j hj.le
  have hcmp := intervalIntegral.integral_mono_on (S.gap_pos j hj).le
    ((affine_ratio_intervalIntegrable (by linarith : 0 < S.φ j)
      (by linarith : 0 < S.p j) (S.gap_pos j hj).le).div_const T)
    ((driftCoeff_continuousOn S hgraph hj).intervalIntegrable (μ := volume)) (fun u hu ↦ ?_)
  · rw [intervalIntegral.integral_div, integral_drift_ratio S hj] at hcmp
    have hh := div_le_div_of_nonneg_right hcmp (S.gap_pos j hj).le
    simpa only [div_right_comm, driftAverage, driftIntegral] using hh
  · have hu0 := hu.1
    have hφu : 0 < S.φ j + u * S.p j := by positivity
    have hτ : 0 < sqrt (σ (driftRatio S j u)) :=
      sqrt_pos.mpr (hgraph _ ((S.ratio_ge_one j hj.le).trans (driftRatio_bounds S hj hu).1)).positive
    change S.p j / (S.φ j + u * S.p j) / T ≤
      S.p j / ((S.φ j + u * S.p j) * sqrt (σ (driftRatio S j u)))
    rw [div_div]
    exact div_le_div_of_nonneg_left (by linarith) (mul_pos hφu hτ)
      (mul_le_mul_of_nonneg_left (hbound u hu) hφu.le)

/-- Integrating an impulse control lower bound retains its exact
reciprocal-slope logarithmic average. -/
theorem impulseAverage_ge_log_of_tau_bound {j : ℕ} (hj : j < N) {T : ℝ} (_hT : 0 ≤ T)
    (hbound : ∀ u ∈ Icc 0 (S.mass (j + 1)), T ≤ sqrt (σ (impulseRatio S j u))) :
    T * (slopeLog S j / S.mass (j + 1)) ≤ impulseAverage S σ j := by
  have hp := (S.state_bounds j hj.le).2.1
  have hφ := (S.state_bounds (j + 1) (by omega)).1
  have hm := S.mass_pos (j + 1) (by omega)
  have hcmp := intervalIntegral.integral_mono_on hm.le
    ((affine_ratio_intervalIntegrable (by linarith : 0 < S.p j)
      (by linarith : 0 < S.φ (j + 1)) hm.le).const_mul T)
    ((impulseCoeff_continuousOn S hgraph hj).intervalIntegrable (μ := volume)) (fun u hu ↦ ?_)
  · rw [intervalIntegral.integral_const_mul, integral_impulse_ratio S hj] at hcmp
    have hh := div_le_div_of_nonneg_right hcmp hm.le
    simpa only [mul_div_assoc, impulseAverage, impulseIntegral] using hh
  · have hu0 := hu.1
    have hp' : 0 < S.p j + u * S.φ (j + 1) := by positivity
    change T * (S.φ (j + 1) / (S.p j + u * S.φ (j + 1))) ≤
      S.φ (j + 1) * sqrt (σ (impulseRatio S j u)) / (S.p j + u * S.φ (j + 1))
    rw [← mul_div_assoc, mul_comm T]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hbound u hu) (by linarith)) hp'.le

variable {B : ℝ} (hB : ∀ r ≥ 1, 0 ≤ logSlope σ r ∧ logSlope σ r ≤ B)
include hB

/-- Exact drift bound based on the following impulse endpoint. -/
theorem driftAverage_exact_ge_end {j : ℕ} (hj : j < N) :
    ((S.p j / S.φ j) * Eminus (driftLog S j)) /
      (sqrt (σ (S.ratio (j + 1))) * exp (B * (energyLog S j - slopeLog S j))) ≤
      driftAverage S σ j := by
  rw [← exact_drift_log_average S hj]
  exact driftAverage_ge_log_of_tau_bound S hgraph hj
    (mul_pos (sqrt_pos.mpr (hgraph _ (S.ratio_ge_one (j + 1) (by omega))).positive) (exp_pos _))
    (fun _ hu ↦ drift_tau_le_end S hgraph hB hj hu)

/-- Exact drift bound based on the beginning of the same drift. -/
theorem driftAverage_exact_ge_start {j : ℕ} (hj : j < N) :
    ((S.p j / S.φ j) * Eminus (driftLog S j)) /
      (sqrt (σ (S.ratio j)) * exp (B * driftLog S j)) ≤ driftAverage S σ j := by
  rw [← exact_drift_log_average S hj]
  exact driftAverage_ge_log_of_tau_bound S hgraph hj
    (mul_pos (sqrt_pos.mpr (hgraph _ (S.ratio_ge_one j hj.le)).positive) (exp_pos _))
    (fun _ hu ↦ drift_tau_le_start S hgraph hB hj hu)

/-- Exact current-impulse bound with its left-slope E-minus factor. -/
theorem impulseAverage_exact_ge_left {j : ℕ} (hj : j < N) :
    sqrt (σ (S.ratio (j + 1))) * ((S.φ (j + 1) / S.p j) * Eminus (slopeLog S j)) ≤
      impulseAverage S σ j := by
  rw [← exact_impulse_log_average_left S hj]
  exact impulseAverage_ge_log_of_tau_bound S hgraph hj (sqrt_nonneg _)
    (fun _ hu ↦ impulse_tau_ge_end S hgraph hB hj hu)

/-- Exact preceding-impulse bound with its right-slope E-plus factor. -/
theorem impulseAverage_exact_ge_right {j : ℕ} (hj : j < N) :
    sqrt (σ (S.ratio (j + 1))) * ((S.φ (j + 1) / S.p (j + 1)) * Eplus (slopeLog S j)) ≤
      impulseAverage S σ j := by
  rw [← exact_impulse_log_average_right S hj]
  exact impulseAverage_ge_log_of_tau_bound S hgraph hj (sqrt_nonneg _)
    (fun _ hu ↦ impulse_tau_ge_end S hgraph hB hj hu)

/-- Full printed bond estimate for the true averages: code uses the
reciprocal of source A-I, hence the source ratio is this actual product. -/
theorem bond_average_exact_bound {j : ℕ} (hj : j < N) :
    exp (-B * (energyLog S j - slopeLog S j)) * Eplus (driftLog S j) * Eminus (slopeLog S j) ≤
      driftAverage S σ j * impulseAverage S σ j := by
  obtain ⟨hφ, hp, _, _⟩ := S.state_bounds j hj.le
  have hφ' := (S.state_bounds (j + 1) (by omega)).1
  have hτ := sqrt_pos.mpr (hgraph _ (S.ratio_ge_one (j + 1) (by omega))).positive
  have hd := driftAverage_exact_ge_end S hgraph hB hj
  have hi := impulseAverage_exact_ge_left S hgraph hB hj
  have hq := Eminus_pos (slopeLog S j)
  have hprod := mul_le_mul hd hi (by positivity) (driftAverage_pos S hgraph hj).le
  have he : (((S.p j / S.φ j) * Eminus (driftLog S j)) /
      (sqrt (σ (S.ratio (j + 1))) * exp (B * (energyLog S j - slopeLog S j)))) *
      (sqrt (σ (S.ratio (j + 1))) * ((S.φ (j + 1) / S.p j) * Eminus (slopeLog S j))) =
      exp (-B * (energyLog S j - slopeLog S j)) * Eplus (driftLog S j) * Eminus (slopeLog S j) := by
    rw [Eplus, show exp (driftLog S j) = S.φ (j + 1) / S.φ j from exp_log (by positivity),
      show -B * (energyLog S j - slopeLog S j) = -(B * (energyLog S j - slopeLog S j)) by ring,
      exp_neg]
    field_simp [hτ.ne', (show S.φ j ≠ 0 by linarith), (show S.p j ≠ 0 by linarith)]
  rwa [he] at hprod

/-- Full printed consecutive-site estimate with E-minus(delta) and the
preceding impulse's E-plus(q). -/
theorem site_average_exact_bound {j : ℕ} (hj : j + 1 < N) :
    exp (-B * driftLog S (j + 1)) * Eminus (driftLog S (j + 1)) * Eplus (slopeLog S j) ≤
      driftAverage S σ (j + 1) * impulseAverage S σ j := by
  obtain ⟨hφ, hp, _, _⟩ := S.state_bounds (j + 1) hj.le
  have hτ := sqrt_pos.mpr (hgraph _ (S.ratio_ge_one (j + 1) hj.le)).positive
  have hd := driftAverage_exact_ge_start S hgraph hB hj
  have hi := impulseAverage_exact_ge_right S hgraph hB (show j < N by omega)
  have hq := Eplus_pos (slopeLog S j)
  have hprod := mul_le_mul hd hi (by positivity) (driftAverage_pos S hgraph hj).le
  have he : (((S.p (j + 1) / S.φ (j + 1)) * Eminus (driftLog S (j + 1))) /
      (sqrt (σ (S.ratio (j + 1))) * exp (B * driftLog S (j + 1)))) *
      (sqrt (σ (S.ratio (j + 1))) * ((S.φ (j + 1) / S.p (j + 1)) * Eplus (slopeLog S j))) =
      exp (-B * driftLog S (j + 1)) * Eminus (driftLog S (j + 1)) * Eplus (slopeLog S j) := by
    rw [show -B * driftLog S (j + 1) = -(B * driftLog S (j + 1)) by ring, exp_neg]
    field_simp [hτ.ne', (show S.φ (j + 1) ≠ 0 by linarith), (show S.p (j + 1) ≠ 0 by linarith)]
  rwa [he] at hprod

end
end krylov.Asymptotics.DiscreteString
