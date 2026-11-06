import nesterov.Flow.Spiral

/-!
Article: Appendix B, Lemma `creduce`.
Use: exact forward and backward convex support discrepancies of the
continuous spirals, with their precise exponential factors.
-/

noncomputable section

namespace nesterov.Flow

open scoped InnerProductSpace

theorem scalar_forward_algebra {c : ℝ} (hc : 0 < c) (θ m γ q : ℝ) :
    (Real.exp (-2 * c * q) - 1) * atomValue θ m c γ -
      ⟪spiralMultiplier θ m c γ, scalarSpiral c γ q - 1⟫_ℝ =
      Real.exp (-c * q) * forwardKernel θ m c γ q := by
  rw [scalarSpiral_forced_inner]
  have he : Real.exp (-2 * c * q) = (Real.exp (c * q) * Real.exp (c * q))⁻¹ := by
    rw [← Real.exp_add, ← Real.exp_neg]
    congr 1
    ring
  rw [he]
  dsimp [atomValue, forwardKernel, kernelA, kernelB]
  rw [Real.cosh_eq, Real.sinh_eq]
  simp only [neg_mul, Real.exp_neg]
  field_simp [ne_of_gt hc, Real.exp_ne_zero]
  ring

theorem scalar_backward_inner (θ m c γ q : ℝ) :
    ⟪spiralMultiplier θ m c γ * scalarSpiral c γ q, 1 - scalarSpiral c γ q⟫_ℝ =
      (γ ^ 2 - delta θ m c) * (Real.exp (-c * q) * Real.cos (γ * q) -
        Real.exp (-2 * c * q)) -
      (2 * c - θ) * γ * Real.exp (-c * q) * Real.sin (γ * q) := by
  rw [inner_sub_right]
  have hself : ⟪spiralMultiplier θ m c γ * scalarSpiral c γ q, scalarSpiral c γ q⟫_ℝ =
      Real.exp (-2 * c * q) * (γ ^ 2 - delta θ m c) := by
    have hh := real_inner_complex_mul (scalarSpiral c γ q) (spiralMultiplier θ m c γ) 1
    simp only [one_mul, scalarSpiral_norm_sq] at hh
    rw [hh, spiralMultiplier_eq]
    simp [real_inner_eq_re_inner, RCLike.inner_apply, pow_two]
  rw [hself, spiralMultiplier_eq]
  simp [real_inner_eq_re_inner, RCLike.inner_apply, pow_two, scalarSpiral_re, scalarSpiral_im]
  ring

theorem scalar_backward_algebra {c : ℝ} (hc : 0 < c) (θ m γ q : ℝ) :
    (1 - Real.exp (-2 * c * q)) * atomValue θ m c γ -
      ⟪spiralMultiplier θ m c γ * scalarSpiral c γ q, 1 - scalarSpiral c γ q⟫_ℝ =
      Real.exp (-c * q) * backwardKernel θ m c γ q := by
  rw [scalar_backward_inner]
  have he : Real.exp (-2 * c * q) = (Real.exp (c * q) * Real.exp (c * q))⁻¹ := by
    rw [← Real.exp_add, ← Real.exp_neg]
    congr 1
    ring
  rw [he]
  dsimp [atomValue, backwardKernel, kernelA, kernelB]
  rw [Real.cosh_eq, Real.sinh_eq]
  simp only [neg_mul, Real.exp_neg]
  field_simp [ne_of_gt hc, Real.exp_ne_zero]
  ring

theorem scalar_distance_algebra (c γ q : ℝ) :
    ‖scalarSpiral c γ q - 1‖ ^ 2 = 2 * Real.exp (-c * q) * kernelA c γ q := by
  rw [norm_sub_sq_real, scalarSpiral_norm_sq]
  have hi : ⟪scalarSpiral c γ q, (1 : ℂ)⟫_ℝ =
      Real.exp (-c * q) * Real.cos (γ * q) := by
    simp only [real_inner_eq_re_inner, RCLike.inner_apply]
    simpa using scalarSpiral_re c γ q
  rw [hi]
  norm_num only [norm_one, one_pow]
  dsimp [kernelA]
  rw [Real.cosh_eq]
  have he : Real.exp (-2 * c * q) = (Real.exp (c * q) * Real.exp (c * q))⁻¹ := by
    rw [← Real.exp_add, ← Real.exp_neg]
    congr 1
    ring
  rw [he]
  simp only [neg_mul, Real.exp_neg]
  field_simp [Real.exp_ne_zero]
  ring

theorem scalar_forward_slack {c : ℝ} (hc : 0 < c) (θ m γ t q : ℝ) :
    Real.exp (-2 * c * (t + q)) * atomValue θ m c γ -
      Real.exp (-2 * c * t) * atomValue θ m c γ -
      ⟪spiralMultiplier θ m c γ * scalarSpiral c γ t,
        scalarSpiral c γ (t + q) - scalarSpiral c γ t⟫_ℝ =
      Real.exp (-2 * c * t - c * q) * forwardKernel θ m c γ q := by
  rw [scalarSpiral_add]
  have he : scalarSpiral c γ q * scalarSpiral c γ t - scalarSpiral c γ t =
      (scalarSpiral c γ q - 1) * scalarSpiral c γ t := by ring
  rw [he, real_inner_complex_mul, scalarSpiral_norm_sq]
  have he2 : Real.exp (-2 * c * (t + q)) =
      Real.exp (-2 * c * t) * Real.exp (-2 * c * q) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he2, Real.exp_sub]
  simp only [div_eq_mul_inv]
  have hh := scalar_forward_algebra hc θ m γ q
  have he3 : Real.exp (-c * q) = (Real.exp (c * q))⁻¹ := by
    rw [← Real.exp_neg]
    congr 1
    ring
  rw [he3] at hh
  linear_combination Real.exp (-2 * c * t) * hh

theorem scalar_backward_slack {c : ℝ} (hc : 0 < c) (θ m γ t q : ℝ) :
    Real.exp (-2 * c * t) * atomValue θ m c γ -
      Real.exp (-2 * c * (t + q)) * atomValue θ m c γ -
      ⟪spiralMultiplier θ m c γ * scalarSpiral c γ (t + q),
        scalarSpiral c γ t - scalarSpiral c γ (t + q)⟫_ℝ =
      Real.exp (-2 * c * t - c * q) * backwardKernel θ m c γ q := by
  rw [scalarSpiral_add]
  have he1 : spiralMultiplier θ m c γ *
      (scalarSpiral c γ q * scalarSpiral c γ t) =
      (spiralMultiplier θ m c γ * scalarSpiral c γ q) * scalarSpiral c γ t := by ring
  have he2 : scalarSpiral c γ t - scalarSpiral c γ q * scalarSpiral c γ t =
      (1 - scalarSpiral c γ q) * scalarSpiral c γ t := by ring
  rw [he1, he2, real_inner_complex_mul, scalarSpiral_norm_sq]
  have he3 : Real.exp (-2 * c * (t + q)) =
      Real.exp (-2 * c * t) * Real.exp (-2 * c * q) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he3, Real.exp_sub]
  simp only [div_eq_mul_inv]
  have hh := scalar_backward_algebra hc θ m γ q
  have he4 : Real.exp (-c * q) = (Real.exp (c * q))⁻¹ := by
    rw [← Real.exp_neg]
    congr 1
    ring
  rw [he4] at hh
  linear_combination Real.exp (-2 * c * t) * hh

theorem real_inner_weighted (r : ℝ) (w a b : ℂ) :
    ⟪w * ((r : ℂ) * a), (r : ℂ) * b - (r : ℂ) * a⟫_ℝ =
      r ^ 2 * ⟪w * a, b - a⟫_ℝ := by
  have h1 : w * ((r : ℂ) * a) = (w * a) * (r : ℂ) := by ring
  have h2 : (r : ℂ) * b - (r : ℂ) * a = (b - a) * (r : ℂ) := by ring
  rw [h1, h2, real_inner_complex_mul]
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs]

variable {J : Type*} [Fintype J]

/-- The first exact lag identity in Lemma `creduce`. -/
theorem Spectrum.forward_slack (ν : Spectrum J) {c : ℝ} (hc : 0 < c) (θ m t q : ℝ) :
    ν.orbitValue θ m c (t + q) - ν.orbitValue θ m c t -
      ⟪ν.forcedGradient θ m c t, ν.orbit c (t + q) - ν.orbit c t⟫_ℝ =
      Real.exp (-2 * c * t - c * q) *
        ∑ j, ν.weight j * forwardKernel θ m c (ν.frequency j) q := by
  rw [PiLp.inner_apply]
  change Real.exp (-2 * c * (t + q)) * (∑ j, ν.weight j * atomValue θ m c (ν.frequency j)) -
    Real.exp (-2 * c * t) * (∑ j, ν.weight j * atomValue θ m c (ν.frequency j)) -
    (∑ j, ⟪spiralMultiplier θ m c (ν.frequency j) *
      ((Real.sqrt (ν.weight j) : ℂ) * scalarSpiral c (ν.frequency j) t),
      (Real.sqrt (ν.weight j) : ℂ) * scalarSpiral c (ν.frequency j) (t + q) -
        (Real.sqrt (ν.weight j) : ℂ) * scalarSpiral c (ν.frequency j) t⟫_ℝ) = _
  simp_rw [real_inner_weighted, Real.sq_sqrt (ν.weight_nonneg _)]
  simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  linear_combination ν.weight j * scalar_forward_slack hc θ m (ν.frequency j) t q

/-- The second exact lag identity in Lemma `creduce`. -/
theorem Spectrum.backward_slack (ν : Spectrum J) {c : ℝ} (hc : 0 < c) (θ m t q : ℝ) :
    ν.orbitValue θ m c t - ν.orbitValue θ m c (t + q) -
      ⟪ν.forcedGradient θ m c (t + q), ν.orbit c t - ν.orbit c (t + q)⟫_ℝ =
      Real.exp (-2 * c * t - c * q) *
        ∑ j, ν.weight j * backwardKernel θ m c (ν.frequency j) q := by
  rw [PiLp.inner_apply]
  change Real.exp (-2 * c * t) * (∑ j, ν.weight j * atomValue θ m c (ν.frequency j)) -
    Real.exp (-2 * c * (t + q)) * (∑ j, ν.weight j * atomValue θ m c (ν.frequency j)) -
    (∑ j, ⟪spiralMultiplier θ m c (ν.frequency j) *
      ((Real.sqrt (ν.weight j) : ℂ) * scalarSpiral c (ν.frequency j) (t + q)),
      (Real.sqrt (ν.weight j) : ℂ) * scalarSpiral c (ν.frequency j) t -
        (Real.sqrt (ν.weight j) : ℂ) * scalarSpiral c (ν.frequency j) (t + q)⟫_ℝ) = _
  simp_rw [real_inner_weighted, Real.sq_sqrt (ν.weight_nonneg _)]
  simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  linear_combination ν.weight j * scalar_backward_slack hc θ m (ν.frequency j) t q

/-- The exact squared-distance identity in Lemma `creduce`. -/
theorem Spectrum.orbit_distance_sq (ν : Spectrum J) (c t q : ℝ) :
    ‖ν.orbit c (t + q) - ν.orbit c t‖ ^ 2 =
      2 * Real.exp (-2 * c * t - c * q) * ∑ j, ν.weight j * kernelA c (ν.frequency j) q := by
  rw [EuclideanSpace.norm_sq_eq]
  change (∑ j, ‖(Real.sqrt (ν.weight j) : ℂ) * scalarSpiral c (ν.frequency j) (t + q) -
    (Real.sqrt (ν.weight j) : ℂ) * scalarSpiral c (ν.frequency j) t‖ ^ 2) = _
  have hid (j : J) : (Real.sqrt (ν.weight j) : ℂ) * scalarSpiral c (ν.frequency j) (t + q) -
      (Real.sqrt (ν.weight j) : ℂ) * scalarSpiral c (ν.frequency j) t =
      (Real.sqrt (ν.weight j) : ℂ) * scalarSpiral c (ν.frequency j) t *
        (scalarSpiral c (ν.frequency j) q - 1) := by
    rw [scalarSpiral_add]
    ring
  simp_rw [hid, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
    sq_abs, Real.sq_sqrt (ν.weight_nonneg _), scalarSpiral_norm_sq, scalar_distance_algebra]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [Real.exp_sub, div_eq_mul_inv]
  have he : Real.exp (-c * q) = (Real.exp (c * q))⁻¹ := by
    rw [← Real.exp_neg]
    congr 1
    ring
  rw [he]
  ring

theorem scalar_minimizer_inner (θ m c γ t : ℝ) :
    ⟪spiralMultiplier θ m c γ * scalarSpiral c γ t, scalarSpiral c γ t⟫_ℝ =
      Real.exp (-2 * c * t) * (γ ^ 2 - delta θ m c) := by
  have hh := real_inner_complex_mul (scalarSpiral c γ t) (spiralMultiplier θ m c γ) 1
  simp only [one_mul, scalarSpiral_norm_sq] at hh
  rw [hh, spiralMultiplier_eq]
  simp [real_inner_eq_re_inner, RCLike.inner_apply, pow_two]

theorem Spectrum.minimizer_inner (ν : Spectrum J) (θ m c t : ℝ) :
    ⟪ν.forcedGradient θ m c t, ν.orbit c t⟫_ℝ =
      Real.exp (-2 * c * t) * ∑ j, ν.weight j * (ν.frequency j ^ 2 - delta θ m c) := by
  rw [PiLp.inner_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  change ⟪spiralMultiplier θ m c (ν.frequency j) *
    ((Real.sqrt (ν.weight j) : ℂ) * scalarSpiral c (ν.frequency j) t),
    (Real.sqrt (ν.weight j) : ℂ) * scalarSpiral c (ν.frequency j) t⟫_ℝ = _
  have hh := real_inner_complex_mul
    ((Real.sqrt (ν.weight j) : ℂ) * scalarSpiral c (ν.frequency j) t)
    (spiralMultiplier θ m c (ν.frequency j)) 1
  simp only [one_mul, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
    sq_abs, Real.sq_sqrt (ν.weight_nonneg j), scalarSpiral_norm_sq] at hh
  rw [hh, spiralMultiplier_eq]
  simp [real_inner_eq_re_inner, RCLike.inner_apply, pow_two]
  ring

/-- The exact minimizer support gap in Lemma `creduce`. -/
theorem Spectrum.minimizer_gap (ν : Spectrum J) {c : ℝ} (hc : 0 < c) (θ m t : ℝ) :
    ⟪ν.forcedGradient θ m c t, ν.orbit c t⟫_ℝ - ν.orbitValue θ m c t =
      Real.exp (-2 * c * t) *
        ∑ j, ν.weight j * atomMinimizerGap θ m c (ν.frequency j) := by
  rw [ν.minimizer_inner]
  dsimp [Spectrum.orbitValue]
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  have hh := atomValue_add_gap (m := m) (θ := θ) (γ := ν.frequency j) hc
  nlinarith [congrArg (fun r : ℝ => ν.weight j * r) hh]

theorem Spectrum.value_ge_minimizer_gap (ν : Spectrum J) {θ m c : ℝ} (hc : 0 < c)
    (hct : c ≤ θ / 2) (t : ℝ) :
    ⟪ν.forcedGradient θ m c t, ν.orbit c t⟫_ℝ - ν.orbitValue θ m c t ≤
      ν.orbitValue θ m c t := by
  rw [ν.minimizer_gap hc]
  dsimp [Spectrum.orbitValue]
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  apply Finset.sum_le_sum
  intro j _
  apply mul_le_mul_of_nonneg_left _ (ν.weight_nonneg j)
  have hh := atomValue_sub_gap (θ := θ) (m := m) (γ := ν.frequency j) hc
  have hn : 0 ≤ (θ - 2 * c) * ν.frequency j ^ 2 / c := by
    apply div_nonneg
    · exact mul_nonneg (by linarith) (sq_nonneg _)
    · exact hc.le
  linarith

end nesterov.Flow
