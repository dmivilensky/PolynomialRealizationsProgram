import Mathlib.Analysis.Real.Pi.Bounds
import polyak.FareyPlateau.LargeCurvature.Constants
import polyak.FareyPlateau.LargeCurvature.ThreeLag

noncomputable section
namespace polyak.FareyPlateau.LargeCurvature
open scoped BigOperators

theorem cutoff_extra_margins {k N A : ℝ} (hk : 5 ≤ k) (hN : 3*k/2 ≤ N)
    (hA : 48*N^2 < A) : 6*Real.pi^2*N/k^2 < A ∧ 24*N/k^2 < A := by
  have hNp : 0 < N := by linarith
  have hk2 : 25 ≤ k^2 := by nlinarith
  have hπ2 : Real.pi^2 < 16 := by nlinarith [Real.pi_lt_four, Real.pi_pos]
  have h₁ : 6*Real.pi^2*N ≤ (48*N^2)*k^2 := by
    have hNN : N ≤ N^2 := by nlinarith
    have hmul := mul_le_mul_of_nonneg_left hk2 (show 0 ≤ 48*N^2 by positivity)
    nlinarith
  have h₂ : 24*N ≤ (48*N^2)*k^2 := by
    have hNN : N ≤ N^2 := by nlinarith
    have hmul := mul_le_mul_of_nonneg_left hk2 (show 0 ≤ 48*N^2 by positivity)
    nlinarith
  constructor <;> apply lt_of_le_of_lt _ hA
  · exact (div_le_iff₀ (by positivity : 0 < k^2)).mpr h₁
  · exact (div_le_iff₀ (by positivity : 0 < k^2)).mpr h₂

theorem central_coefficient_negative {n k s N a h : ℝ}
    (hk : 5 ≤ k) (hnear : |s-n| ≤ k/2) (hN : 3*k/2 ≤ N)
    (ha : Real.pi * centralFactor k h * (9*k^2+3*Real.pi*k) /
      (16*(sineMargin k)^2) < a) :
    -2 * sineMargin k * (a*sineMargin k/centralFactor k h) / Real.pi +
      2 * (∑ i, weight n k s i * deviation n k s i^2) +
      (4/3) * (∑ i, weight n k s i * |deviation n k s i|^3) * zoneRadius k N < 0 := by
  have hkp : 0 < k := by linarith
  have hNp : 0 < N := by linarith
  have hsh := sineMargin_pos hk
  have hH : 0 < centralFactor k h := by unfold centralFactor; positivity
  have ha' := (div_lt_iff₀ (show 0 < 16*(sineMargin k)^2 by positivity)).mp ha
  have hv := variance_upper hkp hnear
  have hu := third_moment_upper hkp hnear
  have hd : zoneRadius k N ≤ 2*Real.pi/(3*k^2) := by
    unfold zoneRadius
    apply (div_le_div_iff₀ (mul_pos hkp hNp) (show 0 < 3*k^2 by positivity)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hN hkp.le, Real.pi_pos]
  have hdpos : 0 ≤ zoneRadius k N := by unfold zoneRadius; positivity
  have hprod := mul_le_mul hu hd hdpos (show 0 ≤ 27/64*k^3 by positivity)
  have he : (27/64*k^3)*(2*Real.pi/(3*k^2)) = 9*Real.pi*k/32 := by field_simp; ring
  rw [he] at hprod
  have hbound : 2*a*(sineMargin k)^2/(Real.pi*centralFactor k h) >
      9*k^2/8+3*Real.pi*k/8 := by
    apply (lt_div_iff₀ (mul_pos Real.pi_pos hH)).mpr
    nlinarith
  have he' : -2 * sineMargin k * (a*sineMargin k/centralFactor k h) / Real.pi =
      -(2*a*(sineMargin k)^2/(Real.pi*centralFactor k h)) := by ring
  rw [he']
  nlinarith

end polyak.FareyPlateau.LargeCurvature
