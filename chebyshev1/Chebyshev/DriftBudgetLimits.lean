import chebyshev1.Chebyshev.DriftBudget
import chebyshev1.Chebyshev.AccuracyScale

/-! Large-condition limits with the actual least integer accuracy horizon. -/
namespace chebyshev1.SpectralInterval
noncomputable section
open Real Filter Topology Polynomial Polynomial.Chebyshev

private theorem dslope_arsinh_limit :
    Tendsto (dslope arsinh 0) (𝓝 (0 : ℝ)) (𝓝 1) := by
  have h := continuousAt_dslope_same.mpr (hasDerivAt_arsinh 0).differentiableAt
  simpa [dslope_same, (hasDerivAt_arsinh 0).deriv] using h.tendsto

/-- The fixed-interval, large-horizon budget in Supplement S3. -/
theorem driftBudget_fixed_interval_limit (I : SpectralInterval) (M : ℝ) :
    Tendsto (fun N : ℕ => (N : ℝ)^2 * I.driftBudget N M)
      atTop (𝓝 (I.delta * arcosh M^2 / 4)) := by
  have hz : Tendsto (fun N : ℕ => arcosh M / (2 * (N : ℝ))) atTop (𝓝 0) := by
    simpa only [div_div] using
      (tendsto_const_nhds (x := arcosh M / 2)).div_atTop tendsto_natCast_atTop_atTop
  have hs : Tendsto (dslope sinh 0) (𝓝 (0 : ℝ)) (𝓝 1) := by
    have hh := continuousAt_dslope_same.mpr (hasDerivAt_sinh 0).differentiableAt
    simpa [dslope_same, (hasDerivAt_sinh 0).deriv] using hh.tendsto
  have hh := ((hs.comp hz).pow 2).const_mul (I.delta * arcosh M^2 / 4)
  simp only [one_pow, mul_one] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have he := sub_smul_dslope sinh 0 (arcosh M / (2 * (N : ℝ)))
  simp only [sub_zero, smul_eq_mul, sinh_zero] at he
  dsimp only [Function.comp_def]
  rw [driftBudget, ← he]
  field_simp
  ring

theorem arcosh_eta_scaled_limit {α : Type*} {l : Filter α}
    {I : α → SpectralInterval} (hK : Tendsto (fun j => (I j).kappa) l atTop) :
    Tendsto (fun j => arcosh (I j).eta * sqrt (I j).kappa) l (𝓝 2) := by
  have hu : Tendsto (fun j => sqrt ((I j).mu / (I j).delta)) l (𝓝 0) := by
    simpa only [gap_ratio_eq, sqrt_zero] using (condition_gap_limit hK).sqrt
  have hg := (tendsto_const_nhds (x := (1 : ℝ))).add (condition_gap_limit hK)
  simp only [add_zero] at hg
  have hp : Tendsto (fun j => sqrt ((I j).mu / (I j).delta) *
      sqrt (I j).kappa) l (𝓝 1) := by
    convert hg.sqrt using 1
    · funext j
      have hk : 0 < (I j).kappa - 1 := sub_pos.mpr (I j).kappa_gt_one
      rw [gap_ratio_eq, ← sqrt_mul (div_nonneg zero_le_one hk.le)]
      congr 1
      field_simp [hk.ne']
      ring
    · simp
  have hh := (dslope_arsinh_limit.comp hu).mul hp
  have hh₂ := hh.const_mul 2
  simp only [mul_one] at hh₂
  apply hh₂.congr
  intro j
  dsimp only [Function.comp_def]
  rw [arcosh_eta, dslope_of_ne _ (sqrt_pos.mpr
    (div_pos (I j).mu_pos (I j).delta_pos)).ne']
  simp only [slope, arsinh_zero, sub_zero, vsub_eq_sub, smul_eq_mul]
  field_simp [(sqrt_pos.mpr (div_pos (I j).mu_pos (I j).delta_pos)).ne']

theorem accuracyHorizon_scaled_limit {α : Type*} {l : Filter α}
    {I : α → SpectralInterval} {epsilon : ℝ} (he : 0 < epsilon) (he1 : epsilon < 1)
    (hK : Tendsto (fun j => (I j).kappa) l atTop) :
    Tendsto (fun j => ((I j).accuracyHorizon epsilon : ℝ) / sqrt (I j).kappa)
      l (𝓝 (arcosh (1 / epsilon) / 2)) := by
  have hlow := (tendsto_const_nhds (x := arcosh (1 / epsilon))).div
    (arcosh_eta_scaled_limit hK) (by norm_num : (2 : ℝ) ≠ 0)
  have hzero : Tendsto (fun j => 1 / sqrt (I j).kappa) l (𝓝 0) :=
    (tendsto_const_nhds (x := (1 : ℝ))).div_atTop (tendsto_sqrt_atTop.comp hK)
  have hupp := hlow.add hzero
  simp only [add_zero] at hupp
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlow hupp ?_ ?_
  · intro j
    dsimp only [Pi.div_apply]
    have hs : 0 < sqrt (I j).kappa := sqrt_pos.mpr (lt_trans zero_lt_one (I j).kappa_gt_one)
    rw [← div_div, div_le_div_iff_of_pos_right hs]
    exact Nat.le_ceil _
  · intro j
    dsimp only [Pi.div_apply]
    have hs : 0 < sqrt (I j).kappa := sqrt_pos.mpr (lt_trans zero_lt_one (I j).kappa_gt_one)
    rw [← div_div, ← add_div, div_le_div_iff_of_pos_right hs]
    apply (Nat.ceil_lt_add_one _).le
    exact div_nonneg (arcosh_nonneg ((one_le_div he).mpr he1.le))
      (arcosh_pos (I j).eta_gt_one).le

theorem accuracyHorizon_atTop {α : Type*} {l : Filter α}
    {I : α → SpectralInterval} {epsilon : ℝ} (he : 0 < epsilon) (he1 : epsilon < 1)
    (hK : Tendsto (fun j => (I j).kappa) l atTop) :
    Tendsto (fun j => ((I j).accuracyHorizon epsilon : ℝ)) l atTop := by
  have ha : 0 < arcosh (1 / epsilon) / 2 :=
    div_pos (arcosh_pos ((one_lt_div he).mpr he1)) (by norm_num)
  have h := (accuracyHorizon_scaled_limit he he1 hK).pos_mul_atTop ha
    (tendsto_sqrt_atTop.comp hK)
  apply h.congr
  intro j
  exact div_mul_cancel₀ _ (sqrt_pos.mpr (lt_trans zero_lt_one (I j).kappa_gt_one)).ne'

theorem accuracyHorizon_amplification_limit {α : Type*} {l : Filter α}
    {I : α → SpectralInterval} {epsilon q : ℝ} (he : 0 < epsilon) (he1 : epsilon < 1)
    (hq : 0 ≤ q) (hK : Tendsto (fun j => (I j).kappa) l atTop) :
    Tendsto (fun j => (T ℝ ((I j).accuracyHorizon epsilon)).eval
      (1 + 2 * q * (I j).mu / (I j).delta)) l
      (𝓝 (cosh (sqrt q * arcosh (1 / epsilon)))) := by
  have h := chebyshev_small_gap_limit hq
    (Eventually.of_forall (fun j => div_nonneg (I j).mu_pos.le (I j).delta_pos.le))
    (show Tendsto (fun j => (I j).mu / (I j).delta) l (𝓝 0) by
      simpa only [gap_ratio_eq] using condition_gap_limit hK)
    (show Tendsto (fun j => ((I j).accuracyHorizon epsilon : ℝ) *
        sqrt ((I j).mu / (I j).delta)) l (𝓝 (arcosh (1 / epsilon) / 2)) by
      simpa only [gap_ratio_eq] using condition_horizon_limit hK
        (accuracyHorizon_scaled_limit he he1 hK))
  convert h using 1
  · funext j
    congr 1
    ring
  · congr 2
    ring

theorem accuracyHorizon_driftBudget_limit {α : Type*} {l : Filter α}
    {I : α → SpectralInterval} {epsilon M : ℝ} (he : 0 < epsilon) (he1 : epsilon < 1)
    (hK : Tendsto (fun j => (I j).kappa) l atTop) :
    Tendsto (fun j => (I j).driftBudget ((I j).accuracyHorizon epsilon) M / (I j).mu)
      l (𝓝 (arcosh M ^ 2 / arcosh (1 / epsilon) ^ 2)) := by
  let N : α → ℕ := fun j => (I j).accuracyHorizon epsilon
  have ha : arcosh (1 / epsilon) ≠ 0 :=
    (arcosh_pos ((one_lt_div he).mpr he1)).ne'
  have hscale := drift_scale_limit (I := I) (N := N)
    (div_ne_zero ha (by norm_num)) hK (accuracyHorizon_scaled_limit he he1 hK)
  have hz : Tendsto (fun j => arcosh M / (2 * (N j : ℝ))) l (𝓝 0) := by
    have h := (tendsto_const_nhds (x := arcosh M / 2)).div_atTop
      (accuracyHorizon_atTop he he1 hK)
    convert h using 1
    funext j
    ring
  have hs : Tendsto (dslope sinh 0) (𝓝 (0 : ℝ)) (𝓝 1) := by
    have h := continuousAt_dslope_same.mpr (hasDerivAt_sinh 0).differentiableAt
    simpa [dslope_same, (hasDerivAt_sinh 0).deriv] using h.tendsto
  have hprod := (hscale.mul_const ((arcosh M / 2) ^ 2)).mul ((hs.comp hz).pow 2)
  have heq : (1 / (arcosh (1 / epsilon) / 2) ^ 2) * (arcosh M / 2) ^ 2 * 1 ^ 2 =
      arcosh M ^ 2 / arcosh (1 / epsilon) ^ 2 := by field_simp
  rw [heq] at hprod
  apply hprod.congr
  intro j
  have hn : (N j : ℝ) ≠ 0 := by exact_mod_cast (accuracyHorizon_pos (I j) he he1).ne'
  have hid := sub_smul_dslope sinh 0 (arcosh M / (2 * (N j : ℝ)))
  simp only [sub_zero, smul_eq_mul, sinh_zero] at hid
  dsimp only [Function.comp_def]
  change (I j).delta / ((I j).mu * (N j : ℝ) ^ 2) * (arcosh M / 2) ^ 2 *
    dslope sinh 0 (arcosh M / (2 * (N j : ℝ))) ^ 2 = _
  rw [driftBudget, ← hid]
  field_simp

end
end chebyshev1.SpectralInterval
