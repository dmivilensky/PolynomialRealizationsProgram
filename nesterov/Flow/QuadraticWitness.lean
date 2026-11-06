import nesterov.Flow.Spiral
import nesterov.Flow.Decay

/-!
Article: Theorem `flow`(b).
Use: actual scalar quadratic solutions, including the oscillatory and
critically damped cases, whose logarithmic state exponent is exactly cQ.
-/

noncomputable section

namespace nesterov.Flow

def realMode (c γ t : ℝ) : ℝ := (scalarSpiral c γ t).re

def realModeVelocity (c γ t : ℝ) : ℝ :=
  (spiralExponent c γ * scalarSpiral c γ t).re

theorem realMode_solution {θ m c γ : ℝ}
    (hchar : spiralExponent c γ ^ 2 + (θ : ℂ) * spiralExponent c γ + (m : ℂ) = 0) :
    IsSolution θ (fun x : ℝ => m / 2 * ‖x‖ ^ 2) (realMode c γ) (realModeVelocity c γ) := by
  constructor
  · intro t _
    exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_scalarSpiral c γ t)
  · intro t _
    have hh := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_scalarSpiral_velocity c γ t)
    have he : spiralExponent c γ ^ 2 * scalarSpiral c γ t =
        -(θ : ℂ) * (spiralExponent c γ * scalarSpiral c γ t) - (m : ℂ) * scalarSpiral c γ t := by
      linear_combination scalarSpiral c γ t * hchar
    rw [he] at hh
    convert hh using 1
    · rfl
    · rw [quadratic_gradient]
      simp [realMode, realModeVelocity]

theorem projection_state_bounds {c γ : ℝ} (hc : 0 ≤ c) (hγ : 0 < γ) (u : ℂ) :
    γ / (γ + c + 1) * ‖u‖ ≤ |u.re| + |(spiralExponent c γ * u).re| ∧
    |u.re| + |(spiralExponent c γ * u).re| ≤ (1 + ‖spiralExponent c γ‖) * ‖u‖ := by
  constructor
  · have hrel : γ * u.im = -(spiralExponent c γ * u).re - c * u.re := by
      simp [spiralExponent]
    have hab : γ * |u.im| ≤ |(spiralExponent c γ * u).re| + c * |u.re| := by
      calc
        _ = |γ * u.im| := by rw [abs_mul, abs_of_pos hγ]
        _ = |-(spiralExponent c γ * u).re - c * u.re| := by rw [hrel]
        _ ≤ |-(spiralExponent c γ * u).re| + |c * u.re| := abs_sub _ _
        _ = _ := by rw [abs_neg, abs_mul, abs_of_nonneg hc]
    have hn := mul_le_mul_of_nonneg_left (Complex.norm_le_abs_re_add_abs_im u) hγ.le
    have hden : 0 < γ + c + 1 := by linarith
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hden).mpr
    have h1 := mul_nonneg (show 0 ≤ γ + c by linarith) (abs_nonneg (spiralExponent c γ * u).re)
    have h2 := abs_nonneg u.re
    nlinarith
  · have h1 := Complex.abs_re_le_norm u
    have h2 := Complex.abs_re_le_norm (spiralExponent c γ * u)
    rw [norm_mul] at h2
    nlinarith

/-- The scalar quadratic witness promised in Theorem flow(b). -/
theorem exists_quadratic_witness {θ m : ℝ} (hθ : 0 < θ) (hm : 0 < m) :
    ∃ x v : ℝ → ℝ,
      IsSolution θ (fun x : ℝ => m / 2 * ‖x‖ ^ 2) x v ∧ x 0 = 1 ∧
        decayExponent x v = (cQ θ m : EReal) := by
  by_cases hu : θ ^ 2 < 4 * m
  · let c := θ / 2
    let γ := Real.sqrt (m - θ ^ 2 / 4)
    have hc : 0 < c := by dsimp [c]; linarith
    have hγ : 0 < γ := Real.sqrt_pos.mpr (by linarith)
    have hs : γ ^ 2 = m - θ ^ 2 / 4 := Real.sq_sqrt (by linarith)
    have hchar : spiralExponent c γ ^ 2 + (θ : ℂ) * spiralExponent c γ + (m : ℂ) = 0 := by
      apply Complex.ext
      · simp [spiralExponent, pow_two]
        dsimp [c]
        nlinarith
      · simp [spiralExponent, pow_two]
        dsimp [c]
        ring
    refine ⟨realMode c γ, realModeVelocity c γ, realMode_solution hchar, ?_, ?_⟩
    · simp [realMode, scalarSpiral_zero]
    · have he : decayExponent (realMode c γ) (realModeVelocity c γ) = (c : EReal) := by
        apply observableExponent_eq_of_two_sided_exp_bounds
          (show 0 < γ / (γ + c + 1) by positivity)
          (show 0 < 1 + ‖spiralExponent c γ‖ by positivity)
        intro t _
        have hh := projection_state_bounds hc.le hγ (scalarSpiral c γ t)
        simpa only [scalarSpiral_norm, Real.norm_eq_abs, realMode, realModeVelocity] using hh
      rw [he]
      congr 1
      exact (cQ_eq_half hu.le).symm
  · let c := cQ θ m
    have hc := cQ_pos hθ hm
    have hd := delta_cQ_eq_zero (show 4 * m ≤ θ ^ 2 by linarith)
    have hchar : spiralExponent c 0 ^ 2 + (θ : ℂ) * spiralExponent c 0 + (m : ℂ) = 0 := by
      apply Complex.ext
      · simp [spiralExponent, pow_two]
        dsimp [delta] at hd
        nlinarith
      · simp [spiralExponent, pow_two]
    refine ⟨realMode c 0, realModeVelocity c 0, realMode_solution hchar, ?_, ?_⟩
    · simp [realMode, scalarSpiral_zero]
    · apply observableExponent_exact_exp (show 0 < 1 + c by dsimp [c]; linarith)
      intro t _
      dsimp [realMode, realModeVelocity]
      rw [scalarSpiral_re]
      simp [c, spiralExponent, scalarSpiral_re, scalarSpiral_im, abs_of_pos hc, mul_comm]
      ring

end nesterov.Flow
