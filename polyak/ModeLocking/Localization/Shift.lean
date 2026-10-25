import polyak.Levels.Threshold.Monoform
import polyak.Global.Symbols.Threshold
import polyak.Farey.Certificates.Polynomial

/-! Exact shift identities for arbitrary finite signed-lag symbols. -/
noncomputable section
namespace polyak.ModeLocking.Localization
open Levels MeasureTheory Set
open scoped BigOperators

variable {I : Type*} [Fintype I]

def symbol (q : General.Tuning) (s : ℝ) (n : I → ℤ) (a : I → ℝ) (γ : ℝ)
    (ω : Frequency) : ℝ :=
  (∑ i, a i * (Geometry.shiftedCurve q s).lag (n i) ω) +
    γ * (Geometry.shiftedCurve q s).minimizer ω

def oscillation (n : I → ℤ) (a : I → ℝ) (ω : Frequency) : ℝ :=
  ∑ i, a i * (1 - Real.cos ((n i : ℝ) * (ω : ℝ)))

theorem phase_sin_pos (q : General.Tuning) (s : ℝ) (ω : Frequency)
    (hω : ω ∈ Threshold.interiorCarrier) :
    0 < Real.sin (Geometry.shiftedCurve q s ω) :=
  Real.sin_pos_of_pos_of_lt_pi (Geometry.shiftedAngle_mem q s hω).1
    (Geometry.shiftedAngle_mem q s hω).2

theorem lag_div_sin (q : General.Tuning) (s : ℝ) (n : ℤ) (ω : Frequency)
    (hω : ω ∈ Threshold.interiorCarrier) :
    (Geometry.shiftedCurve q s).lag n ω / Real.sin (Geometry.shiftedCurve q s ω) =
      Threshold.monotoneLag (Threshold.shiftedCotangent q s) n ω := by
  rw [Curve.lag_expand, sub_div, mul_div_right_comm,
    mul_div_cancel_left₀ _ (phase_sin_pos q s ω hω).ne']
  rw [Geometry.shiftedCurve_apply, Geometry.cot_shiftedAngle q s hω]
  rfl

theorem symbol_div_sin (q : General.Tuning) (s : ℝ) (n : I → ℤ) (a : I → ℝ)
    (γ : ℝ) (ω : Frequency) (hω : ω ∈ Threshold.interiorCarrier) :
    symbol q s n a γ ω / Real.sin (Geometry.shiftedCurve q s ω) =
      (∑ i, a i * Threshold.monotoneLag (Threshold.shiftedCotangent q s) (n i) ω) +
        γ * Threshold.shiftedCotangent q s ω := by
  unfold symbol
  rw [add_div, Finset.sum_div, mul_div_assoc]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    rw [mul_div_assoc, lag_div_sin q s (n i) ω hω]
  · congr 1
    exact Geometry.cot_shiftedAngle q s hω

theorem shift_identity (q : General.Tuning) (s t : ℝ) (n : I → ℤ) (a : I → ℝ)
    (γ : ℝ) (ω : Frequency) (hω : ω ∈ Threshold.interiorCarrier) :
    symbol q s n a γ ω / Real.sin (Geometry.shiftedCurve q s ω) =
      symbol q t n a γ ω / Real.sin (Geometry.shiftedCurve q t ω) +
        (s - t) * (oscillation n a ω + γ) := by
  rw [symbol_div_sin q s n a γ ω hω, symbol_div_sin q t n a γ ω hω]
  unfold Threshold.monotoneLag Threshold.shiftedCotangent oscillation
  have he : (∑ i, a i * ((Geometry.cotangent q ω + s) *
      (1 - Real.cos ((n i : ℝ) * (ω : ℝ))) - Real.sin ((n i : ℝ) * (ω : ℝ)))) =
      (∑ i, a i * ((Geometry.cotangent q ω + t) *
      (1 - Real.cos ((n i : ℝ) * (ω : ℝ))) - Real.sin ((n i : ℝ) * (ω : ℝ)))) +
        (s-t) * ∑ i, a i * (1-Real.cos ((n i : ℝ)*(ω : ℝ))) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he]
  ring

theorem symbol_zero (q : General.Tuning) (s : ℝ) (n : I → ℤ) (a : I → ℝ) (γ : ℝ) :
    symbol q s n a γ frequencyZero = -γ := by simp [symbol]

theorem symbol_pi (q : General.Tuning) (s : ℝ) (n : I → ℤ) (a : I → ℝ) (γ : ℝ) :
    symbol q s n a γ frequencyPi =
      (∑ i, a i * (-1 + Real.cos ((n i : ℝ)*Real.pi))) - γ := by
  simp only [symbol, Curve.lag_at_pi, Curve.minimizer_at_pi, mul_neg, mul_one]
  ring

theorem symbol_pi_shift (q : General.Tuning) (s t : ℝ) (n : I → ℤ) (a : I → ℝ) (γ : ℝ) :
    symbol q s n a γ frequencyPi = symbol q t n a γ frequencyPi := by
  rw [symbol_pi, symbol_pi]

theorem oscillation_nonneg (n : I → ℤ) (a : I → ℝ) (ha : ∀ i, 0 ≤ a i)
    (ω : Frequency) : 0 ≤ oscillation n a ω :=
  Finset.sum_nonneg fun i _ => mul_nonneg (ha i) (sub_nonneg.mpr (Real.cos_le_one _))

theorem oscillation_add_gamma_le_two (n : I → ℤ) (a : I → ℝ) (γ : ℝ)
    (ha : ∀ i, 0 ≤ a i) (hγ : 0 ≤ γ) (hnorm : (∑ i, a i)+γ=1)
    (ω : Frequency) : oscillation n a ω + γ ≤ 2 := by
  have hs : oscillation n a ω ≤ ∑ i, 2*a i :=
    Finset.sum_le_sum fun i _ => by nlinarith [ha i, Real.neg_one_le_cos ((n i : ℝ)*(ω : ℝ))]
  rw [← Finset.mul_sum] at hs
  nlinarith

end polyak.ModeLocking.Localization
