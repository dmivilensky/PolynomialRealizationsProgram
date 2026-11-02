import krylov.Asymptotics.DesignUpperBound
import krylov.Asymptotics.RecoveryMesh
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import chebyshev1.Chebyshev.DriftScale

/-!
Article: main_krylov, thm:limit, scaled upper limit and logarithmic error.
Use: the literal finite-kappa upper bound has the correct sharp limit and
an actual `O(theta log(1/theta))` remainder. All estimates concern the
original hyperbolic spacing and actual spectral interval.
Source: the exact spacing dictionary, elementary logarithmic estimates
and the standard x log(x) limit from mathlib.
-/

namespace krylov.Asymptotics
noncomputable section
open Real Filter Set
open krylov.Design krylov.ContinuumControl
open scoped Topology

/-- The exact additive part of the scaled source upper bound. -/
def upperRemainder (I : chebyshev1.SpectralInterval) (γ B : ℝ) : ℝ :=
  designSpacing I * ((1 + B) / 4 * log I.kappa + 1 / 2 + (1 + 2 * B) / (4 * γ))

theorem spacing_mul_sqrt_le_two (I : chebyshev1.SpectralInterval) :
    designSpacing I * sqrt (I.kappa - 1) ≤ 2 := by
  exact (mul_le_mul_of_nonneg_right (designSpacing_bounds I).2 (sqrt_nonneg _)).trans_eq
    (div_mul_cancel₀ 2 (sqrt_pos.mpr (sub_pos.mpr I.kappa_gt_one)).ne')

/-- The condition number is at most five divided by the squared spacing
once the actual spacing is at most one. -/
theorem log_kappa_le_spacing (I : chebyshev1.SpectralInterval) (hθ : designSpacing I ≤ 1) :
    log I.kappa ≤ log 5 + 2 * log (1 / designSpacing I) := by
  have hp := designSpacing_pos I
  have hR : 0 ≤ I.kappa - 1 := sub_nonneg.mpr I.kappa_gt_one.le
  have hs := pow_le_pow_left₀ (mul_nonneg hp.le (sqrt_nonneg _)) (spacing_mul_sqrt_le_two I) 2
  rw [mul_pow, sq_sqrt hR] at hs
  have hk : I.kappa ≤ 5 / designSpacing I ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hp)).2
    have hsq : designSpacing I ^ 2 ≤ 1 := pow_le_one₀ hp.le hθ
    nlinarith
  have hl := log_le_log (zero_lt_one.trans I.kappa_gt_one) hk
  rw [log_div (by norm_num : (5 : ℝ) ≠ 0) (pow_ne_zero 2 hp.ne'), log_pow] at hl
  norm_num only [Nat.cast_ofNat] at hl
  rw [one_div, log_inv]
  linarith

/-- A positive explicit common remainder constant. -/
def upperRemainderConstant (γ B : ℝ) : ℝ :=
  (1 + B) / 4 * (log 5 + 2) + (1 / 2 + (1 + 2 * B) / (4 * γ)) + 1

/-- The true scaled remainder has a pointwise logarithmic estimate on an
explicit small-spacing neighborhood. -/
theorem upperRemainder_bound (I : chebyshev1.SpectralInterval) {γ B : ℝ}
    (hγ : 0 < γ) (hB : 0 ≤ B) (hsmall : designSpacing I ≤ exp (-1)) :
    0 ≤ upperRemainder I γ B ∧ upperRemainder I γ B ≤
      upperRemainderConstant γ B * (designSpacing I * log (1 / designSpacing I)) := by
  have hp := designSpacing_pos I
  have hlogκ : 0 ≤ log I.kappa := log_nonneg I.kappa_gt_one.le
  have hθ₁ : designSpacing I ≤ 1 := hsmall.trans (exp_le_one_iff.mpr (by norm_num))
  have hlogθ : 1 ≤ log (1 / designSpacing I) := by
    have hh := (log_le_iff_le_exp hp).2 hsmall
    rw [one_div, log_inv]
    linarith
  have ha : 0 ≤ (1 + B) / 4 := by positivity
  have hd : 0 ≤ 1 / 2 + (1 + 2 * B) / (4 * γ) := by positivity
  refine ⟨by unfold upperRemainder; positivity, ?_⟩
  have hl := log_kappa_le_spacing I hθ₁
  have hl5 : 0 ≤ log (5 : ℝ) := log_nonneg (by norm_num)
  have he : (1 + B) / 4 * log I.kappa + 1 / 2 + (1 + 2 * B) / (4 * γ) ≤
      upperRemainderConstant γ B * log (1 / designSpacing I) := by
    have h₁ := mul_le_mul_of_nonneg_left hl ha
    have h₂ := mul_le_mul_of_nonneg_left hlogθ hd
    have h₃ := mul_le_mul_of_nonneg_left hlogθ (mul_nonneg ha hl5)
    dsimp only [upperRemainderConstant]
    nlinarith
  exact (mul_le_mul_of_nonneg_left he hp.le).trans_eq (by ring)

/-- The literal scaled bound is at most the genuine continuum value plus
its actual logarithmic remainder. -/
theorem finiteDesignUpper_scaled_le (I : chebyshev1.SpectralInterval) {γ B : ℝ} {σ : ℝ → ℝ}
    (hf : 0 ≤ feedbackValue γ σ 1) :
    designSpacing I * finiteDesignUpper I γ B σ ≤ feedbackValue γ σ 1 + upperRemainder I γ B := by
  have hh := mul_le_mul_of_nonneg_right (spacing_mul_sqrt_le_two I) hf
  unfold finiteDesignUpper upperRemainder
  nlinarith

/-- The original spacing tends to zero as the condition number diverges. -/
theorem designSpacing_tendsto_zero {α : Type*} {l : Filter α}
    {I : α → chebyshev1.SpectralInterval} (hκ : Tendsto (fun a ↦ (I a).kappa) l atTop) :
    Tendsto (fun a ↦ designSpacing (I a)) l (𝓝 0) := by
  have hR : Tendsto (fun a ↦ (I a).kappa - 1) l atTop := by
    simpa only [sub_eq_add_neg] using tendsto_atTop_add_const_right l (-1 : ℝ) hκ
  simpa only [Function.comp_def, gapSpacing_eq_designSpacing] using gapSpacing_tendsto_zero.comp hR

/-- Replacing the spectral gap by the condition number leaves the exact
leading conversion unchanged. -/
theorem spacing_mul_sqrt_kappa_tendsto {α : Type*} {l : Filter α}
    {I : α → chebyshev1.SpectralInterval} (hκ : Tendsto (fun a ↦ (I a).kappa) l atTop) :
    Tendsto (fun a ↦ designSpacing (I a) * sqrt (I a).kappa) l (𝓝 2) := by
  have hR : Tendsto (fun a ↦ (I a).kappa - 1) l atTop := by
    simpa only [sub_eq_add_neg] using tendsto_atTop_add_const_right l (-1 : ℝ) hκ
  have hs := gapSpacing_mul_sqrt_tendsto.comp hR
  simp only [Function.comp_def, gapSpacing_eq_designSpacing] at hs
  have hh := ((hs.pow 2).add ((designSpacing_tendsto_zero hκ).pow 2)).sqrt
  norm_num at hh
  apply hh.congr
  intro a
  apply (sq_eq_sq₀ (sqrt_nonneg _) (mul_nonneg (designSpacing_pos (I a)).le (sqrt_nonneg _))).mp
  rw [sq_sqrt (by positivity)]
  simp only [mul_pow, sq_sqrt (zero_lt_one.trans (I a).kappa_gt_one).le,
    sq_sqrt (sub_pos.mpr (I a).kappa_gt_one).le]
  ring

/-- The displayed big-O remainder is a genuine filter-level estimate,
valid uniformly along arbitrary diverging condition numbers. -/
theorem upperRemainder_isBigO {α : Type*} {l : Filter α}
    {I : α → chebyshev1.SpectralInterval} (hκ : Tendsto (fun a ↦ (I a).kappa) l atTop)
    {γ B : ℝ} (hγ : 0 < γ) (hB : 0 ≤ B) :
    (fun a ↦ upperRemainder (I a) γ B) =O[l]
      (fun a ↦ designSpacing (I a) * log (1 / designSpacing (I a))) := by
  have hθ := designSpacing_tendsto_zero hκ
  apply Asymptotics.IsBigO.of_bound (upperRemainderConstant γ B)
  filter_upwards [(tendsto_order.1 hθ).2 (exp (-1)) (exp_pos _)] with a ha
  have hb := upperRemainder_bound (I a) hγ hB ha.le
  rw [Real.norm_of_nonneg hb.1, Real.norm_of_nonneg]
  · exact hb.2
  · have hp := designSpacing_pos (I a)
    have hsmall := ha.le.trans (exp_le_one_iff.mpr (by norm_num : (-1 : ℝ) ≤ 0))
    exact mul_nonneg hp.le (log_nonneg ((one_le_div hp).2 hsmall))

/-- The literal theta-logarithm remainder scale tends to zero. -/
theorem spacing_log_tendsto_zero {α : Type*} {l : Filter α}
    {I : α → chebyshev1.SpectralInterval} (hκ : Tendsto (fun a ↦ (I a).kappa) l atTop) :
    Tendsto (fun a ↦ designSpacing (I a) * log (1 / designSpacing (I a))) l (𝓝 0) := by
  have hθ : Tendsto (fun a ↦ designSpacing (I a)) l (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨designSpacing_tendsto_zero hκ,
      Filter.Eventually.of_forall fun a ↦ designSpacing_pos (I a)⟩
  have hh := (tendsto_log_mul_rpow_nhdsGT_zero zero_lt_one).comp hθ
  simpa only [Function.comp_def, rpow_one, one_div, log_inv, mul_neg, mul_comm, neg_zero] using hh.neg

/-- The actual finite-kappa comparison function converges to the same
continuum constant as the matching recovery construction. -/
theorem finiteDesignUpper_scaled_tendsto {α : Type*} {l : Filter α}
    {I : α → chebyshev1.SpectralInterval} (hκ : Tendsto (fun a ↦ (I a).kappa) l atTop)
    {γ B : ℝ} (hγ : 0 < γ) (hB : 0 ≤ B) (σ : ℝ → ℝ) :
    Tendsto (fun a ↦ designSpacing (I a) * finiteDesignUpper (I a) γ B σ) l
      (𝓝 (feedbackValue γ σ 1)) := by
  have hR : Tendsto (fun a ↦ (I a).kappa - 1) l atTop := by
    simpa only [sub_eq_add_neg] using tendsto_atTop_add_const_right l (-1 : ℝ) hκ
  have hs := gapSpacing_mul_sqrt_tendsto.comp hR
  simp only [Function.comp_def, gapSpacing_eq_designSpacing] at hs
  have hr := (upperRemainder_isBigO hκ hγ hB).trans_tendsto (spacing_log_tendsto_zero hκ)
  have hh := ((hs.mul_const (feedbackValue γ σ 1)).div_const 2).add hr
  rw [show 2 * feedbackValue γ σ 1 / 2 + 0 = feedbackValue γ σ 1 by ring] at hh
  apply hh.congr
  intro a
  have he : designSpacing (I a) * finiteDesignUpper (I a) γ B σ =
      designSpacing (I a) * sqrt ((I a).kappa - 1) * feedbackValue γ σ 1 / 2 + upperRemainder (I a) γ B := by
    unfold finiteDesignUpper upperRemainder
    ring
  exact he.symm

end
end krylov.Asymptotics
