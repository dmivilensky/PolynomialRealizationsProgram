import krylov.Asymptotics.ExactAveragesFunctions

/-!
Article: main_krylov, apC:lem:step, exact drift and impulse integrals.
Use: compute the literal reciprocal-affine integrals and all three
normalized averages appearing in the printed bond/site products.
Source: FTC for log of a positive affine function and the discrete recurrence.
-/

namespace krylov.Asymptotics.ExactAverages
noncomputable section
open Real Set MeasureTheory
open krylov.Strings
open scoped Topology

/-- The true reciprocal-affine integrand is integrable on every positive
finite interval; both affine coefficients are strictly positive. -/
theorem affine_ratio_intervalIntegrable {a b l : ℝ} (ha : 0 < a) (hb : 0 < b) (hl : 0 ≤ l) :
    IntervalIntegrable (fun u ↦ b / (a + u * b)) volume 0 l := by
  apply ContinuousOn.intervalIntegrable (μ := volume)
  intro u hu
  have hu0 : 0 ≤ u := by rw [uIcc_of_le hl] at hu; exact hu.1
  have hc : ContinuousAt (fun v : ℝ ↦ a + v * b) u := by fun_prop
  exact (continuousAt_const.div hc (ne_of_gt (by positivity : 0 < a + u * b))).continuousWithinAt

/-- The exact ordinary logarithmic integral behind every drift and
impulse average in the source. -/
theorem integral_affine_ratio {a b l : ℝ} (ha : 0 < a) (hb : 0 < b) (hl : 0 ≤ l) :
    (∫ u in (0 : ℝ)..l, b / (a + u * b)) = log ((a + l * b) / a) := by
  have hd (u : ℝ) (hu : u ∈ uIcc (0 : ℝ) l) :
      HasDerivAt (fun u ↦ log (a + u * b)) (b / (a + u * b)) u := by
    have hu0 : 0 ≤ u := by rw [uIcc_of_le hl] at hu; exact hu.1
    convert (((hasDerivAt_id u).mul_const b).const_add a).log
      (ne_of_gt (by positivity : 0 < a + u * b)) using 1 <;> simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (affine_ratio_intervalIntegrable ha hb hl),
    log_div (by positivity) ha.ne']
  simp

/-- Normalize the exact affine logarithmic integral at its left state. -/
theorem affine_log_average_left {a b l : ℝ} (ha : 0 < a) (hb : 0 < b) (hl : 0 < l) :
    log ((a + l * b) / a) / l = (b / a) * Eminus (log ((a + l * b) / a)) := by
  have hr : 1 < (a + l * b) / a := (one_lt_div ha).mpr (by linarith [mul_pos hl hb])
  have hd := log_pos hr
  rw [Eminus_eq hd.ne', exp_log (zero_lt_one.trans hr)]
  field_simp [ha.ne', hl.ne']
  ring

/-- Normalize the same exact affine logarithmic integral at its right
state; this is the source's preceding-impulse E-plus factor. -/
theorem affine_log_average_right {a b l : ℝ} (ha : 0 < a) (hb : 0 < b) (hl : 0 < l) :
    log ((a + l * b) / a) / l =
      (b / (a + l * b)) * Eplus (log ((a + l * b) / a)) := by
  rw [affine_log_average_left ha hb hl, Eplus, exp_log (by positivity)]
  field_simp

end
end krylov.Asymptotics.ExactAverages

namespace krylov.Asymptotics.DiscreteString
noncomputable section
open Real Set MeasureTheory ExactAverages
open krylov.Strings
open scoped Topology
variable {N : ℕ} (S : krylov.Strings.DiscreteString N)

/-- The actual drift's reciprocal-position integral is its true positive
log increment, with no endpoint approximation. -/
theorem integral_drift_ratio {j : ℕ} (hj : j < N) :
    (∫ u in (0 : ℝ)..S.gap j, S.p j / (S.φ j + u * S.p j)) = driftLog S j := by
  obtain ⟨hφ, hp, _, _⟩ := S.state_bounds j hj.le
  rw [integral_affine_ratio (by linarith : 0 < S.φ j) (by linarith : 0 < S.p j)
    (S.gap_pos j hj).le, ← S.φ_succ]
  rfl

/-- The actual impulse's reciprocal-slope integral is its true positive
log increment, with its correct pre-mass slope. -/
theorem integral_impulse_ratio {j : ℕ} (hj : j < N) :
    (∫ u in (0 : ℝ)..S.mass (j + 1), S.φ (j + 1) / (S.p j + u * S.φ (j + 1))) =
      slopeLog S j := by
  have hp := (S.state_bounds j hj.le).2.1
  have hφ := (S.state_bounds (j + 1) (by omega)).1
  rw [integral_affine_ratio (by linarith : 0 < S.p j) (by linarith : 0 < S.φ (j + 1))
    (S.mass_pos (j + 1) (by omega)).le, ← S.p_succ]
  rfl

/-- The printed exact free-drift average with E-minus(delta). -/
theorem exact_drift_log_average {j : ℕ} (hj : j < N) :
    driftLog S j / S.gap j = (S.p j / S.φ j) * Eminus (driftLog S j) := by
  obtain ⟨hφ, hp, _, _⟩ := S.state_bounds j hj.le
  have hh := affine_log_average_left (by linarith : 0 < S.φ j)
    (by linarith : 0 < S.p j) (S.gap_pos j hj)
  rw [← S.φ_succ] at hh
  exact hh

/-- The printed exact current-impulse average with E-minus(q). -/
theorem exact_impulse_log_average_left {j : ℕ} (hj : j < N) :
    slopeLog S j / S.mass (j + 1) =
      (S.φ (j + 1) / S.p j) * Eminus (slopeLog S j) := by
  have hp := (S.state_bounds j hj.le).2.1
  have hφ := (S.state_bounds (j + 1) (by omega)).1
  have hh := affine_log_average_left (by linarith : 0 < S.p j)
    (by linarith : 0 < S.φ (j + 1)) (S.mass_pos (j + 1) (by omega))
  rw [← S.p_succ] at hh
  exact hh

/-- The exact preceding-impulse average uses its right slope and E-plus(q). -/
theorem exact_impulse_log_average_right {j : ℕ} (hj : j < N) :
    slopeLog S j / S.mass (j + 1) =
      (S.φ (j + 1) / S.p (j + 1)) * Eplus (slopeLog S j) := by
  have hp := (S.state_bounds j hj.le).2.1
  have hφ := (S.state_bounds (j + 1) (by omega)).1
  have hh := affine_log_average_right (by linarith : 0 < S.p j)
    (by linarith : 0 < S.φ (j + 1)) (S.mass_pos (j + 1) (by omega))
  rw [← S.p_succ] at hh
  exact hh

end
end krylov.Asymptotics.DiscreteString
