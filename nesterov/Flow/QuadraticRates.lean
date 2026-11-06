import nesterov.Flow.QuadraticWitness

/-!
Article: Theorem `flow`(b,d), quadratic sharpness for state, gap, and energy.
Use: a real Hilbert plane gives nonvanishing exact-exponential quadratic
values, so the upper bounds on all three worst-case exponents are literal.
-/

noncomputable section

namespace nesterov.Flow

theorem exists_quadratic_frequency {θ m : ℝ} (_hθ : 0 < θ) (_hm : 0 < m) :
    ∃ γ : ℝ, 0 ≤ γ ∧ spiralExponent (cQ θ m) γ ^ 2 +
      (θ : ℂ) * spiralExponent (cQ θ m) γ + (m : ℂ) = 0 := by
  by_cases hu : θ ^ 2 < 4 * m
  · let γ := Real.sqrt (m - θ ^ 2 / 4)
    have hs : γ ^ 2 = m - θ ^ 2 / 4 := Real.sq_sqrt (by linarith)
    refine ⟨γ, Real.sqrt_nonneg _, ?_⟩
    rw [cQ_eq_half hu.le]
    apply Complex.ext
    · simp [spiralExponent, pow_two]
      nlinarith
    · simp [spiralExponent, pow_two]
      ring
  · refine ⟨0, le_rfl, ?_⟩
    have hd := delta_cQ_eq_zero (show 4 * m ≤ θ ^ 2 by linarith)
    apply Complex.ext
    · simp [spiralExponent, pow_two]
      dsimp [delta] at hd
      nlinarith
    · simp [spiralExponent, pow_two]

theorem complexMode_solution {θ m c γ : ℝ}
    (hchar : spiralExponent c γ ^ 2 + (θ : ℂ) * spiralExponent c γ + (m : ℂ) = 0) :
    IsSolution θ (fun x : ℂ => m / 2 * ‖x‖ ^ 2) (scalarSpiral c γ)
      (fun t => spiralExponent c γ * scalarSpiral c γ t) := by
  constructor
  · intro t _
    exact hasDerivAt_scalarSpiral c γ t
  · intro t _
    rw [quadratic_gradient]
    have he : -(θ : ℂ) * (spiralExponent c γ * scalarSpiral c γ t) -
        (m : ℂ) * scalarSpiral c γ t = spiralExponent c γ ^ 2 * scalarSpiral c γ t := by
      linear_combination -scalarSpiral c γ t * hchar
    simp only [Complex.real_smul, Complex.ofReal_neg]
    rw [he]
    exact hasDerivAt_scalarSpiral_velocity c γ t

/-- One actual finite-smoothness quadratic objective has the exact three
exponents cQ,2cQ,2cQ, including underdamped and critical damping. -/
theorem exists_quadratic_all_exponents {θ m : ℝ} (hθ : 0 < θ) (hm : 0 < m) :
    ∃ x v : ℝ → ℂ,
      IsSolution θ (fun z : ℂ => m / 2 * ‖z‖ ^ 2) x v ∧ ‖x 0‖ = 1 ∧
      decayExponent x v = (cQ θ m : EReal) ∧
      observableExponent (fun t => m / 2 * ‖x t‖ ^ 2) = ((2 * cQ θ m : ℝ) : EReal) ∧
      observableExponent (fun t => energy (fun z : ℂ => m / 2 * ‖z‖ ^ 2) (x t) (v t)) =
        ((2 * cQ θ m : ℝ) : EReal) := by
  obtain ⟨γ, _, hchar⟩ := exists_quadratic_frequency hθ hm
  let c := cQ θ m
  let z := spiralExponent c γ
  let x := scalarSpiral c γ
  let v := fun t => z * x t
  refine ⟨x, v, complexMode_solution hchar, ?_, ?_, ?_, ?_⟩
  · simp [x, scalarSpiral_zero]
  · apply observableExponent_exact_exp (show 0 < 1 + ‖z‖ by positivity)
    intro t _
    change ‖scalarSpiral c γ t‖ + ‖z * scalarSpiral c γ t‖ = _
    rw [norm_mul, scalarSpiral_norm]
    ring
  · apply observableExponent_exact_exp (show 0 < m / 2 by linarith)
    intro t _
    change m / 2 * ‖scalarSpiral c γ t‖ ^ 2 = m / 2 * Real.exp (-(2 * c) * t)
    rw [scalarSpiral_norm_sq]
    congr 2
    ring
  · apply observableExponent_exact_exp (show 0 < m / 2 + ‖z‖ ^ 2 / 2 by positivity)
    intro t _
    change m / 2 * ‖scalarSpiral c γ t‖ ^ 2 + ‖z * scalarSpiral c γ t‖ ^ 2 / 2 = _
    rw [norm_mul, mul_pow, scalarSpiral_norm_sq]
    have he : -2 * c * t = -(2 * c) * t := by ring
    rw [he]
    ring

end nesterov.Flow
