import krylov.Asymptotics.StepAverages

/-!
Article: main_krylov, upper-bound proof after apC:lem:step.
Use: the actual integrated averages satisfy the logarithmic bond and site
bounds with the printed sharp coefficients. These bounds follow directly
from the proved pointwise drift/impulse bounds, so they require neither an
assumed averaging certificate nor division by a possibly zero logarithm.
Source: positivity of interval integration and elementary exp/log algebra.
-/
namespace krylov.Asymptotics
noncomputable section
open Real Set MeasureTheory
open krylov.Strings krylov.ContinuumControl
open scoped Topology

/-- Pointwise lower bounds pass to the true interval average. -/
theorem interval_average_ge {f : ℝ → ℝ} {l c : ℝ} (hl : 0 < l)
    (hi : IntervalIntegrable f volume 0 l) (h : ∀ u ∈ Icc 0 l, c ≤ f u) :
    c ≤ (∫ u in 0..l, f u) / l := by
  have hcmp := intervalIntegral.integral_mono_on hl.le intervalIntegrable_const hi h
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at hcmp
  exact (le_div_iff₀ hl).2 (by nlinarith only [hcmp])

namespace DiscreteString
variable {N : ℕ} (S : krylov.Strings.DiscreteString N)
variable {γ : ℝ} {σ : ℝ → ℝ} (hgraph : ∀ r ≥ 1, FeedbackGraphAt γ σ r)
include hgraph

/-- Positivity of the true drift average. -/
theorem driftAverage_pos {j : ℕ} (hj : j < N) : 0 < driftAverage S σ j :=
  div_pos (driftIntegral_pos S hgraph hj) (S.gap_pos j hj)

/-- Positivity of the true impulse average. -/
theorem impulseAverage_pos {j : ℕ} (hj : j < N) : 0 < impulseAverage S σ j :=
  div_pos (impulseIntegral_pos S hgraph hj) (S.mass_pos (j + 1) (by omega))

variable {B : ℝ} (hB : ∀ r ≥ 1, 0 ≤ logSlope σ r ∧ logSlope σ r ≤ B)
include hB

/-- Actual mean drift bound based on the following post-mass state. -/
theorem driftAverage_ge_end {j : ℕ} (hj : j < N) :
    S.p j / (S.φ (j + 1) * sqrt (σ (S.ratio (j + 1))) *
      exp (B * (energyLog S j - slopeLog S j))) ≤ driftAverage S σ j :=
  interval_average_ge (S.gap_pos j hj)
    ((driftCoeff_continuousOn S hgraph hj).intervalIntegrable (μ := volume))
    (fun _ hu ↦ driftCoeff_ge_end S hgraph hB hj hu)

/-- Actual mean drift bound based on its initial post-mass state. -/
theorem driftAverage_ge_start {j : ℕ} (hj : j < N) :
    S.p j / (S.φ (j + 1) * sqrt (σ (S.ratio j)) * exp (B * driftLog S j)) ≤
      driftAverage S σ j :=
  interval_average_ge (S.gap_pos j hj)
    ((driftCoeff_continuousOn S hgraph hj).intervalIntegrable (μ := volume))
    (fun _ hu ↦ driftCoeff_ge_start S hgraph hB hj hu)

/-- Actual mean impulse bound based on its terminal post-mass state. -/
theorem impulseAverage_ge_end {j : ℕ} (hj : j < N) :
    S.φ (j + 1) * sqrt (σ (S.ratio (j + 1))) / S.p (j + 1) ≤ impulseAverage S σ j :=
  interval_average_ge (S.mass_pos (j + 1) (by omega))
    ((impulseCoeff_continuousOn S hgraph hj).intervalIntegrable (μ := volume))
    (fun _ hu ↦ impulseCoeff_ge_end S hgraph hB hj hu)

/-- The source logarithmic bond estimate for the true pair of averages. -/
theorem bond_average_log_bound {j : ℕ} (hj : j < N) :
    -B * energyLog S j - (1 - B) * slopeLog S j ≤
      log (driftAverage S σ j * impulseAverage S σ j) := by
  obtain ⟨_, hp, _, _⟩ := S.state_bounds j hj.le
  obtain ⟨hφ', hp', _, _⟩ := S.state_bounds (j + 1) (by omega)
  have hτ := sqrt_pos.mpr (hgraph _ (S.ratio_ge_one (j + 1) (by omega))).positive
  have hD := driftAverage_ge_end S hgraph hB hj
  have hI := impulseAverage_ge_end S hgraph hB hj
  have hprod := mul_le_mul hD hI
    (show 0 ≤ S.φ (j + 1) * sqrt (σ (S.ratio (j + 1))) / S.p (j + 1) by positivity)
    (driftAverage_pos S hgraph hj).le
  have he : exp (-B * energyLog S j - (1 - B) * slopeLog S j) =
      (S.p j / (S.φ (j + 1) * sqrt (σ (S.ratio (j + 1))) *
        exp (B * (energyLog S j - slopeLog S j)))) *
      (S.φ (j + 1) * sqrt (σ (S.ratio (j + 1))) / S.p (j + 1)) := by
    have hq : exp (slopeLog S j) = S.p (j + 1) / S.p j :=
      exp_log (div_pos (by linarith) (by linarith))
    have harg : -B * energyLog S j - (1 - B) * slopeLog S j =
        -(B * (energyLog S j - slopeLog S j)) - slopeLog S j := by ring
    rw [harg, exp_sub, exp_neg, hq]
    field_simp
  rw [← he] at hprod
  have hlog := log_le_log (exp_pos _) hprod
  rwa [log_exp] at hlog

/-- The consecutive-step site estimate retains the exact source coefficient
`1+B`; the neighboring impulse is the genuine preceding one. -/
theorem site_average_log_bound {j : ℕ} (hj : j + 1 < N) :
    -(1 + B) * driftLog S (j + 1) ≤
      log (driftAverage S σ (j + 1) * impulseAverage S σ j) := by
  obtain ⟨hφ, hp, _, _⟩ := S.state_bounds (j + 1) hj.le
  have hφ' := (S.state_bounds (j + 2) (by omega)).1
  have hτ := sqrt_pos.mpr (hgraph _ (S.ratio_ge_one (j + 1) hj.le)).positive
  have hD := driftAverage_ge_start S hgraph hB hj
  have hI := impulseAverage_ge_end S hgraph hB (show j < N by omega)
  have hprod := mul_le_mul hD hI
    (show 0 ≤ S.φ (j + 1) * sqrt (σ (S.ratio (j + 1))) / S.p (j + 1) by positivity)
    (driftAverage_pos S hgraph hj).le
  have he : exp (-(1 + B) * driftLog S (j + 1)) =
      (S.p (j + 1) / (S.φ ((j + 1) + 1) * sqrt (σ (S.ratio (j + 1))) *
        exp (B * driftLog S (j + 1)))) *
      (S.φ (j + 1) * sqrt (σ (S.ratio (j + 1))) / S.p (j + 1)) := by
    have hq : exp (driftLog S (j + 1)) = S.φ ((j + 1) + 1) / S.φ (j + 1) :=
      exp_log (div_pos (by simpa only [Nat.add_assoc] using (show 0 < S.φ (j + 2) by linarith))
        (by linarith))
    have harg : -(1 + B) * driftLog S (j + 1) =
        -(B * driftLog S (j + 1)) - driftLog S (j + 1) := by ring
    rw [harg, exp_sub, exp_neg, hq]
    field_simp
  rw [← he] at hprod
  have hlog := log_le_log (exp_pos _) hprod
  rwa [log_exp] at hlog

end DiscreteString
end
end krylov.Asymptotics
