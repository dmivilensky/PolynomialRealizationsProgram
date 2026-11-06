import chebyshev1.Chebyshev.DriftBudgetLimits

/-! Small-accuracy limits for the exact inverse-hyperbolic accuracy parameter. -/
namespace chebyshev1
noncomputable section
open Real Filter Topology

theorem exp_arcosh_accuracy_ratio {epsilon : ℝ} (he : 0 < epsilon) (he1 : epsilon ≤ 1) :
    exp (arcosh (1 / epsilon)) / (2 / epsilon) = (1 + sqrt (1 - epsilon ^ 2)) / 2 := by
  have hr : 0 ≤ 1 - epsilon ^ 2 := by nlinarith
  rw [exp_arcosh ((one_le_div he).mpr he1),
    show (1 / epsilon) ^ 2 - 1 = (1 - epsilon ^ 2) / epsilon ^ 2 by field_simp,
    sqrt_div hr, sqrt_sq he.le]
  field_simp

theorem exp_arcosh_accuracy_ratio_limit :
    Tendsto (fun epsilon : ℝ => exp (arcosh (1 / epsilon)) / (2 / epsilon))
      (𝓝[>] 0) (𝓝 1) := by
  have hid : Tendsto (fun epsilon : ℝ => epsilon) (𝓝[>] 0) (𝓝 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  have h := ((tendsto_const_nhds (x := (1 : ℝ))).add
    (((tendsto_const_nhds (x := (1 : ℝ))).sub (hid.pow 2)).sqrt)).div_const 2
  simp only [zero_pow (by norm_num : 2 ≠ 0), sub_zero, sqrt_one] at h
  norm_num at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds]
      with epsilon he he1
  exact (exp_arcosh_accuracy_ratio he he1.le).symm

theorem arcosh_accuracy_atTop :
    Tendsto (fun epsilon : ℝ => arcosh (1 / epsilon)) (𝓝[>] 0) atTop := by
  apply tendsto_exp_comp_atTop.mp
  refine tendsto_atTop_mono' _ ?_ (by simpa only [one_div] using tendsto_inv_nhdsGT_zero)
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds]
      with epsilon he he1
  rw [exp_arcosh ((one_le_div he).mpr he1.le)]
  simpa only [one_div] using le_add_of_nonneg_right (a := 1 / epsilon) (sqrt_nonneg ((1 / epsilon) ^ 2 - 1))

theorem arcosh_accuracy_log_ratio_limit :
    Tendsto (fun epsilon : ℝ => arcosh (1 / epsilon) / log (2 / epsilon))
      (𝓝[>] 0) (𝓝 1) := by
  have hlog := (continuousAt_log one_ne_zero).tendsto.comp exp_arcosh_accuracy_ratio_limit
  simp only [log_one] at hlog
  have hden : Tendsto (fun epsilon : ℝ => log (2 / epsilon)) (𝓝[>] 0) atTop := by
    have h := tendsto_inv_nhdsGT_zero.const_mul_atTop (by norm_num : (0 : ℝ) < 2)
    simpa only [Function.comp_def, div_eq_mul_inv] using tendsto_log_atTop.comp h
  have h := (tendsto_const_nhds (x := (1 : ℝ))).add (hlog.div_atTop hden)
  simp only [add_zero] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds]
      with epsilon he he1
  have hepos : 0 < epsilon := he
  have hd : 0 < log (2 / epsilon) := log_pos ((one_lt_div hepos).mpr (by linarith))
  dsimp only [Function.comp_def]
  rw [log_div (exp_ne_zero _) (by positivity), log_exp]
  field_simp
  ring

/-- The exact limiting drift budget has the logarithmic accuracy scale. -/
theorem driftBudget_log_accuracy_limit (M : ℝ) :
    Tendsto (fun epsilon : ℝ =>
      (arcosh M ^ 2 / arcosh (1 / epsilon) ^ 2) * log (2 / epsilon) ^ 2)
      (𝓝[>] 0) (𝓝 (arcosh M ^ 2)) := by
  have h := (arcosh_accuracy_log_ratio_limit.inv₀ one_ne_zero).pow 2
  have hh := h.const_mul (arcosh M ^ 2)
  simp only [inv_one, one_pow, mul_one] at hh
  apply hh.congr
  intro epsilon
  simp only [inv_div, div_pow]
  ring

/-- The exponential approximation uses a strictly positive drift fraction. -/
theorem exact_low_accuracy_amplification_ratio_limit {q : ℝ} (hq : 0 < q) :
    Tendsto (fun epsilon : ℝ => cosh (sqrt q * arcosh (1 / epsilon)) /
      ((1 / 2 : ℝ) * (2 / epsilon) ^ sqrt q)) (𝓝[>] 0) (𝓝 1) := by
  have harg := arcosh_accuracy_atTop.const_mul_atTop (sqrt_pos.mpr hq)
  have hcosh := cosh_exp_ratio_limit.comp harg
  have hpow := exp_arcosh_accuracy_ratio_limit.rpow_const (p := sqrt q) (Or.inl one_ne_zero)
  simp only [one_rpow] at hpow
  have h := hcosh.mul hpow
  simp only [mul_one] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds]
      with epsilon he he1
  have hepos : 0 < epsilon := he
  dsimp only [Function.comp_def]
  rw [div_rpow (exp_pos _).le (by positivity : (0 : ℝ) ≤ 2 / epsilon),
    ← exp_mul]
  rw [mul_comm (arcosh (1 / epsilon)) (sqrt q)]
  field_simp

theorem zero_drift_amplification (epsilon : ℝ) :
    cosh (sqrt (0 : ℝ) * arcosh (1 / epsilon)) = 1 := by simp

end
end chebyshev1
