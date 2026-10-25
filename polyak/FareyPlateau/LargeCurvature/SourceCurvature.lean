import polyak.FareyPlateau.Domain.Phase
import polyak.Levels.Geometry.Convexity

/-! The central-zone lower curvature bound is derived from the actual
quadratic profile and endpoint signs of a tuning. -/
noncomputable section
namespace polyak.FareyPlateau.LargeCurvature
open General Levels Set

theorem profile_upper (q : Tuning) {c₀ h₀ a D M : ℝ}
    (he : Chart.coefficients q = edgeCoefficients c₀ h₀ a D)
    (hM : 0 ≤ M) (hD : |D| ≤ M) (ha : (1 + M)^2 / 4 ≤ a) (hap : 0 < a)
    (c : ℝ) : q.Xi c ≤ h₀ + 1 := by
  have hD' := abs_le.mp hD
  have hsq : (1 + D)^2 ≤ (1 + M)^2 := by
    have h : |1 + D| ≤ 1 + M := abs_le.mpr ⟨by linarith [hD'.1], by linarith [hD'.2]⟩
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (by linarith : 0 ≤ 1 + M)).mpr h
  rw [← Chart.eval_coefficients, he, edgeCoefficients_eval]
  have hcomp := sq_nonneg (2 * a * (c - c₀) - (1 + D))
  have hmul := mul_nonneg hap.le (by linarith [ha, hsq] : 0 ≤ 4 * a - (1 + D)^2)
  nlinarith

theorem cotangent_negative_curvature_lower (q : Tuning) {c₀ h₀ a D : ℝ}
    (he : Chart.coefficients q = edgeCoefficients c₀ h₀ a D)
    {ω : ℝ} (hω : ω ∈ Ioo (0 : ℝ) Real.pi) :
    a * Real.sin ω ≤ -Geometry.cotangentSecond q ω := by
  have hs := Real.sin_pos_of_pos_of_lt_pi hω.1 hω.2
  have hid := Geometry.cotangentSecond_endpoint_identity q hω
  rw [Geometry.deriv2_cotangent q hω, he] at hid
  change Geometry.cotangentSecond q ω * (Real.sin ω)^3 =
    (1 / 2 : ℝ) * (1 + Real.cos ω)^2 * q.Xi 1 +
    (1 / 2 : ℝ) * (1 - Real.cos ω)^2 * q.Xi (-1) + (-a) * (1 - (Real.cos ω)^2)^2 at hid
  have hp := mul_nonpos_of_nonneg_of_nonpos
    (show 0 ≤ (1 / 2 : ℝ) * (1 + Real.cos ω)^2 by positivity) q.Xi_one_neg.le
  have hm := mul_nonpos_of_nonneg_of_nonpos
    (show 0 ≤ (1 / 2 : ℝ) * (1 - Real.cos ω)^2 by positivity) q.Xi_neg_one_neg.le
  have hs2 : 1 - (Real.cos ω)^2 = (Real.sin ω)^2 := by
    nlinarith [Real.sin_sq_add_cos_sq ω]
  rw [hs2] at hid
  have hprod : (a * Real.sin ω + Geometry.cotangentSecond q ω) * (Real.sin ω)^3 ≤ 0 := by
    nlinarith [hid]
  have hn := nonpos_of_mul_nonpos_left hprod (pow_pos hs 3)
  linarith

theorem phase_second_lower (q : Tuning) {c₀ h₀ a D M sh : ℝ}
    (he : Chart.coefficients q = edgeCoefficients c₀ h₀ a D)
    (hh : 0 ≤ h₀) (hM : 0 ≤ M) (hD : |D| ≤ M)
    (ha : (1 + M)^2 / 4 ≤ a) (hap : 0 < a) (hsh : 0 < sh)
    {ω : ℝ} (hω : ω ∈ Ioo (0 : ℝ) Real.pi)
    (hsin : sh ≤ Real.sin ω) (hphase : Geometry.shiftedAngle q 0 ω ≤ Real.pi / 2) :
    a * sh / (1 + (h₀ + 1)^2 / sh^2) ≤ deriv^[2] (Geometry.shiftedAngle q 0) ω := by
  have hs := Real.sin_pos_of_pos_of_lt_pi hω.1 hω.2
  have hcot : 0 ≤ Geometry.cotangent q ω := by
    simpa only [add_zero] using (Geometry.shiftedAngle_le_half_pi_iff q 0 hω).mp hphase
  have hupper : Geometry.cotangent q ω ≤ (h₀ + 1) / sh := by
    unfold Geometry.cotangent
    apply (div_le_div_of_nonneg_right (profile_upper q he hM hD ha hap _) hs.le).trans
    exact div_le_div_of_nonneg_left (by linarith : 0 ≤ h₀ + 1) hsh hsin
  have hsquare : (Geometry.cotangent q ω)^2 ≤ (h₀ + 1)^2 / sh^2 := by
    rw [← div_pow]
    exact (sq_le_sq₀ hcot (div_nonneg (by linarith) hsh.le)).mpr hupper
  have hn := cotangent_negative_curvature_lower q he hω
  have hsmall : a * sh ≤ -Geometry.cotangentSecond q ω :=
    (mul_le_mul_of_nonneg_left hsin hap.le).trans hn
  have hden : 0 < 1 + (Geometry.cotangent q ω)^2 := by positivity
  have hlarge : 0 < 1 + (h₀ + 1)^2 / sh^2 := by positivity
  have hbound : a * sh / (1 + (h₀ + 1)^2 / sh^2) ≤
      -Geometry.cotangentSecond q ω / (1 + (Geometry.cotangent q ω)^2) := by
    apply (div_le_div_iff₀ hlarge hden).mpr
    have hmul := mul_le_mul_of_nonneg_left (add_le_add_left hsquare 1) (mul_nonneg hap.le hsh.le)
    have hn' := mul_le_mul_of_nonneg_right hsmall hlarge.le
    nlinarith [hmul, hn']
  rw [Geometry.deriv2_shiftedAngle q 0 hω, Geometry.shiftedSecond]
  simp only [add_zero]
  exact hbound.trans (le_add_of_nonneg_right (by positivity))

end polyak.FareyPlateau.LargeCurvature
