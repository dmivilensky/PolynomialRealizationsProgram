import krylov.Asymptotics.StepLoss
import krylov.Asymptotics.LogLipschitz

/-!
Article: main_krylov, apC:lem:step, consecutive-step averaging.
Use: actual drift and impulse coefficients have the uniform endpoint
bounds forced by the sharp logarithmic graph regularity. Their integrated
averages give the bond/site estimates used in the sharp finite-κ bound.
Source: the proved log-Lipschitz theorem and positivity of interval integrals.
-/
namespace krylov.Asymptotics
noncomputable section
open Real Set MeasureTheory
open krylov.Strings krylov.ContinuumControl
open scoped Topology

namespace DiscreteString
variable {N : ℕ} (S : krylov.Strings.DiscreteString N)

/-- The actual ratio just before the next mass, after the free drift. -/
def driftEndRatio (j : ℕ) : ℝ := S.φ (j + 1) * S.p j / S.K j
/-- Actual mean drift coefficient. -/
def driftAverage (σ : ℝ → ℝ) (j : ℕ) : ℝ := driftIntegral S σ j / S.gap j
/-- Actual mean impulse coefficient; the source's `Aᴵ` is its reciprocal. -/
def impulseAverage (σ : ℝ → ℝ) (j : ℕ) : ℝ := impulseIntegral S σ j / S.mass (j + 1)

/-- Exact ratio logarithm between the beginning and end of the free drift. -/
theorem driftEnd_log_start {j : ℕ} (hj : j < N) :
    log (driftEndRatio S j / S.ratio j) = driftLog S j := by
  obtain ⟨hφ, hp, hK, _⟩ := S.state_bounds j hj.le
  unfold driftLog
  congr 1
  dsimp [driftEndRatio, krylov.Strings.DiscreteString.ratio]
  field_simp

/-- Exact decrease of log-ratio across the next actual impulse. -/
theorem driftEnd_log_end {j : ℕ} (hj : j < N) :
    log (driftEndRatio S j / S.ratio (j + 1)) = energyLog S j - slopeLog S j := by
  obtain ⟨_, hp, hK, _⟩ := S.state_bounds j hj.le
  obtain ⟨hφ', hp', hK', _⟩ := S.state_bounds (j + 1) (by omega)
  have he : driftEndRatio S j / S.ratio (j + 1) =
      (S.K (j + 1) / S.K j) / (S.p (j + 1) / S.p j) := by
    dsimp [driftEndRatio, krylov.Strings.DiscreteString.ratio]
    field_simp
  rw [he, log_div (div_ne_zero (by linarith) (by linarith))
    (div_ne_zero (by linarith) (by linarith))]
  rfl

variable {γ B : ℝ} {σ : ℝ → ℝ}
    (hgraph : ∀ r ≥ 1, FeedbackGraphAt γ σ r)
    (hB : ∀ r ≥ 1, 0 ≤ logSlope σ r ∧ logSlope σ r ≤ B)
include hgraph hB

/-- The drift's optimal control is bounded using the beginning of that drift. -/
theorem drift_tau_le_start {j : ℕ} (hj : j < N) {u : ℝ} (hu : u ∈ Icc 0 (S.gap j)) :
    sqrt (σ (driftRatio S j u)) ≤ sqrt (σ (S.ratio j)) * exp (B * driftLog S j) := by
  have hr := S.ratio_ge_one j hj.le
  have hbounds := driftRatio_bounds S hj hu
  have hend : S.ratio j ≤ driftEndRatio S j := by
    simpa only [driftRatio, driftEndRatio, ← S.φ_succ] using
      (driftRatio_bounds S hj (show S.gap j ∈ Icc 0 (S.gap j) from
        ⟨(S.gap_pos j hj).le, le_rfl⟩)).1
  have hmono := sqrt_monotoneOn_of_logSlope (fun r hr ↦ (hgraph r hr).positive)
    (fun r hr ↦ (hgraph r hr).differentiable) hB
  have h₁ := hmono (hr.trans hbounds.1) (hr.trans hend) hbounds.2
  have h₂ := sqrt_mul_bound_of_logSlope (fun r hr ↦ (hgraph r hr).positive)
    (fun r hr ↦ (hgraph r hr).differentiable) hB hr hend
  rw [driftEnd_log_start S hj] at h₂
  exact h₁.trans h₂

/-- The same drift has the alternative bound based on the end of its impulse. -/
theorem drift_tau_le_end {j : ℕ} (hj : j < N) {u : ℝ} (hu : u ∈ Icc 0 (S.gap j)) :
    sqrt (σ (driftRatio S j u)) ≤
      sqrt (σ (S.ratio (j + 1))) * exp (B * (energyLog S j - slopeLog S j)) := by
  have hr := S.ratio_ge_one (j + 1) (by omega)
  have hbounds := driftRatio_bounds S hj hu
  have hzero : (0 : ℝ) ∈ Icc 0 (S.mass (j + 1)) := ⟨le_rfl, (S.mass_pos (j + 1) (by omega)).le⟩
  have hend : S.ratio (j + 1) ≤ driftEndRatio S j := by
    simpa only [impulseRatio, driftEndRatio, zero_mul, add_zero] using
      (impulseRatio_bounds S hj hzero).1
  have hmono := sqrt_monotoneOn_of_logSlope (fun r hr ↦ (hgraph r hr).positive)
    (fun r hr ↦ (hgraph r hr).differentiable) hB
  have h₁ := hmono ((S.ratio_ge_one j hj.le).trans hbounds.1) (hr.trans hend) hbounds.2
  have h₂ := sqrt_mul_bound_of_logSlope (fun r hr ↦ (hgraph r hr).positive)
    (fun r hr ↦ (hgraph r hr).differentiable) hB hr hend
  rw [driftEnd_log_end S hj] at h₂
  exact h₁.trans h₂

/-- The impulse control is bounded below by its actual post-mass control. -/
theorem impulse_tau_ge_end {j : ℕ} (hj : j < N) {u : ℝ}
    (hu : u ∈ Icc 0 (S.mass (j + 1))) :
    sqrt (σ (S.ratio (j + 1))) ≤ sqrt (σ (impulseRatio S j u)) := by
  have hr := S.ratio_ge_one (j + 1) (by omega)
  have hb := (impulseRatio_bounds S hj hu).1
  exact sqrt_monotoneOn_of_logSlope (fun r hr ↦ (hgraph r hr).positive)
    (fun r hr ↦ (hgraph r hr).differentiable) hB hr (hr.trans hb) hb

/-- Pointwise lower drift coefficient based on the post-impulse endpoint. -/
theorem driftCoeff_ge_end {j : ℕ} (hj : j < N) {u : ℝ} (hu : u ∈ Icc 0 (S.gap j)) :
    S.p j / (S.φ (j + 1) * sqrt (σ (S.ratio (j + 1))) *
      exp (B * (energyLog S j - slopeLog S j))) ≤ driftCoeff S σ j u := by
  obtain ⟨hφ, hp, _, _⟩ := S.state_bounds j hj.le
  have hφ' := (S.state_bounds (j + 1) (by omega)).1
  have hu₀ := hu.1
  have hφu : 0 < S.φ j + u * S.p j := by positivity
  have hτ := sqrt_pos.mpr (hgraph _ ((S.ratio_ge_one j hj.le).trans (driftRatio_bounds S hj hu).1)).positive
  have hτ' := sqrt_pos.mpr (hgraph _ (S.ratio_ge_one (j + 1) (by omega))).positive
  have hφle : S.φ j + u * S.p j ≤ S.φ (j + 1) := by
    rw [S.φ_succ]
    nlinarith [mul_nonneg (sub_nonneg.mpr hu.2) (show 0 ≤ S.p j by linarith)]
  have hτle := drift_tau_le_end S hgraph hB hj hu
  have hden := mul_le_mul hφle hτle hτ.le (show 0 ≤ S.φ (j + 1) by linarith)
  dsimp [driftCoeff]
  apply (div_le_div_iff₀ (by positivity) (mul_pos hφu hτ)).2
  nlinarith only [mul_nonneg (show 0 ≤ S.p j by linarith) (sub_nonneg.mpr hden)]

/-- Pointwise lower drift coefficient based on the beginning of the drift. -/
theorem driftCoeff_ge_start {j : ℕ} (hj : j < N) {u : ℝ} (hu : u ∈ Icc 0 (S.gap j)) :
    S.p j / (S.φ (j + 1) * sqrt (σ (S.ratio j)) * exp (B * driftLog S j)) ≤
      driftCoeff S σ j u := by
  obtain ⟨hφ, hp, _, _⟩ := S.state_bounds j hj.le
  have hφ' := (S.state_bounds (j + 1) (by omega)).1
  have hu₀ := hu.1
  have hφu : 0 < S.φ j + u * S.p j := by positivity
  have hτ := sqrt_pos.mpr (hgraph _ ((S.ratio_ge_one j hj.le).trans (driftRatio_bounds S hj hu).1)).positive
  have hτ' := sqrt_pos.mpr (hgraph _ (S.ratio_ge_one j hj.le)).positive
  have hφle : S.φ j + u * S.p j ≤ S.φ (j + 1) := by
    rw [S.φ_succ]
    nlinarith [mul_nonneg (sub_nonneg.mpr hu.2) (show 0 ≤ S.p j by linarith)]
  have hτle := drift_tau_le_start S hgraph hB hj hu
  have hden := mul_le_mul hφle hτle hτ.le (show 0 ≤ S.φ (j + 1) by linarith)
  dsimp [driftCoeff]
  apply (div_le_div_iff₀ (by positivity) (mul_pos hφu hτ)).2
  nlinarith only [mul_nonneg (show 0 ≤ S.p j by linarith) (sub_nonneg.mpr hden)]

/-- Pointwise lower impulse coefficient at its post-mass endpoint. -/
theorem impulseCoeff_ge_end {j : ℕ} (hj : j < N) {u : ℝ}
    (hu : u ∈ Icc 0 (S.mass (j + 1))) :
    S.φ (j + 1) * sqrt (σ (S.ratio (j + 1))) / S.p (j + 1) ≤ impulseCoeff S σ j u := by
  have hφ := (S.state_bounds (j + 1) (by omega)).1
  have hp := (S.state_bounds j hj.le).2.1
  have hp' := (S.state_bounds (j + 1) (by omega)).2.1
  have hu₀ := hu.1
  have hpu : 0 < S.p j + u * S.φ (j + 1) := by positivity
  have hτ := sqrt_pos.mpr (hgraph _ (S.ratio_ge_one (j + 1) (by omega))).positive
  have hτle := impulse_tau_ge_end S hgraph hB hj hu
  have hple : S.p j + u * S.φ (j + 1) ≤ S.p (j + 1) := by
    rw [S.p_succ]
    nlinarith [mul_nonneg (sub_nonneg.mpr hu.2) (show 0 ≤ S.φ (j + 1) by linarith)]
  dsimp [impulseCoeff]
  calc
    S.φ (j + 1) * sqrt (σ (S.ratio (j + 1))) / S.p (j + 1) ≤
        S.φ (j + 1) * sqrt (σ (S.ratio (j + 1))) / (S.p j + u * S.φ (j + 1)) := by
      gcongr
    _ ≤ _ := by gcongr

end DiscreteString
end
end krylov.Asymptotics
