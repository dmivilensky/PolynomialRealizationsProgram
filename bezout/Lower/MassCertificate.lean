import bezout.Lower.MassEnergy

/-!
Article: bezout, Lemma C.1 (`lem:two-masses`).
Use: a pointwise certificate for the signed mass energy replaces the
constrained-minimization argument by finite inequalities. The two cones are
separated by `u = 2 v`; their integer populations detect the odd-horizon gap.
No existence or stationarity assumption on an optimizer is used.
-/

namespace bezout.Lower

noncomputable section

/-- The first cone has an exact supporting quadratic whenever the two rates
are sufficiently close. The numerical rational bounds are uniform in the
horizon and include the smallest odd horizon. -/
theorem massEnergy_certificate_left (a b u v : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hba : b ≤ 8 / 5 * a) (hab : a ≤ 5 / 4 * b) (huv : 2 * v ≤ u) :
    2 * a * u + 2 * b * v - a ^ 2 ≤ massEnergy u v := by
  by_cases hv : 0 ≤ v
  · have hu : 0 ≤ u := by linarith
    rw [massEnergy_of_mul_nonneg (mul_nonneg hu hv)]
    have hC : 0 ≤ 9 * a ^ 2 - 4 * a * b - b ^ 2 := by
      have h := mul_nonneg (sub_nonneg.mpr hba)
        (show 0 ≤ b + 28 / 5 * a by positivity)
      nlinarith [sq_nonneg a]
    have hq : 0 ≤ a ^ 2 * (u ^ 2 + v ^ 2 + 4 * u * v) - (a * u + b * v) ^ 2 := by
      have h₁ : 0 ≤ 2 * a * (2 * a - b) * v * (u - 2 * v) := by
        have : 0 ≤ 2 * a - b := by linarith
        positivity
      have h₂ := mul_nonneg hC (sq_nonneg v)
      nlinarith only [h₁, h₂]
    have h : 0 ≤ a ^ 2 * (u ^ 2 + v ^ 2 + 4 * u * v -
        (2 * a * u + 2 * b * v - a ^ 2)) := by
      nlinarith only [hq, sq_nonneg (a * u + b * v - a ^ 2)]
    exact sub_nonneg.mp (nonneg_of_mul_nonneg_right h (sq_pos_of_pos ha))
  · have hv' : v < 0 := lt_of_not_ge hv
    by_cases hu : u ≤ 0
    · have hn := massEnergy_nonneg u v
      have h₁ := mul_nonpos_of_nonneg_of_nonpos ha.le hu
      have h₂ := mul_nonpos_of_nonneg_of_nonpos hb.le hv'.le
      nlinarith [sq_nonneg a]
    · have hu' : 0 < u := lt_of_not_ge hu
      rw [massEnergy_of_mul_nonpos (mul_nonpos_of_nonneg_of_nonpos hu'.le hv'.le)]
      have hcross : 0 ≤ (a - 2 * b) * v := by
        apply mul_nonneg_of_nonpos_of_nonpos <;> linarith
      nlinarith only [sq_nonneg (u - a + v / 2), sq_nonneg v, hcross]

/-- The supporting quadratic on the complementary cone has the other rate
as its intercept. This asymmetric partition is what works at every odd N. -/
theorem massEnergy_certificate_right (a b u v : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hba : b ≤ 8 / 5 * a) (hab : a ≤ 5 / 4 * b) (huv : u ≤ 2 * v) :
    2 * a * u + 2 * b * v - b ^ 2 ≤ massEnergy u v := by
  by_cases hu : 0 ≤ u
  · have hv : 0 ≤ v := by linarith
    rw [massEnergy_of_mul_nonneg (mul_nonneg hu hv)]
    have hC : 0 ≤ 3 * b ^ 2 - a * b - a ^ 2 := by
      have h := mul_nonneg (sub_nonneg.mpr hab)
        (show 0 ≤ a + 9 / 4 * b by positivity)
      nlinarith [sq_nonneg b]
    have hq : 0 ≤ b ^ 2 * (u ^ 2 + v ^ 2 + 4 * u * v) - (a * u + b * v) ^ 2 := by
      have h₁ : 0 ≤ b * (2 * b - a) * u * (2 * v - u) := by
        have : 0 ≤ 2 * b - a := by linarith
        positivity
      have h₂ := mul_nonneg hC (sq_nonneg u)
      nlinarith only [h₁, h₂]
    have h : 0 ≤ b ^ 2 * (u ^ 2 + v ^ 2 + 4 * u * v -
        (2 * a * u + 2 * b * v - b ^ 2)) := by
      nlinarith only [hq, sq_nonneg (a * u + b * v - b ^ 2)]
    exact sub_nonneg.mp (nonneg_of_mul_nonneg_right h (sq_pos_of_pos hb))
  · have hu' : u < 0 := lt_of_not_ge hu
    by_cases hv : v ≤ 0
    · have hn := massEnergy_nonneg u v
      have h₁ := mul_nonpos_of_nonneg_of_nonpos ha.le hu'.le
      have h₂ := mul_nonpos_of_nonneg_of_nonpos hb.le hv
      nlinarith [sq_nonneg b]
    · have hv' : 0 < v := lt_of_not_ge hv
      rw [massEnergy_of_mul_nonpos (mul_nonpos_of_nonpos_of_nonneg hu'.le hv'.le)]
      have hcross : 0 ≤ (b - 2 * a) * u := by
        apply mul_nonneg_of_nonpos_of_nonpos <;> linarith
      nlinarith only [sq_nonneg (v - b + u / 2), sq_nonneg u, hcross]

end
end bezout.Lower
