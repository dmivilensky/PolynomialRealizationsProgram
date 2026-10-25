import polyak.Boundary.P1.FiniteSource

/-! Article: the two P1 equalities and the sole endpoint-active second upper lag. -/
namespace polyak.Boundary.P1
noncomputable section

theorem scaledSlack_one_lower (z a : ℝ) : scaledSlack 1 (-1) z a=0 := by
  rw [← polynomialSlack_eq]
  norm_num [polynomialSlack,radialT,radialU,plainT,plainU]
  ring

theorem scaledSlack_three_upper (z a : ℝ) : scaledSlack 3 1 z a=0 := by
  rw [← polynomialSlack_eq]
  norm_num [polynomialSlack,radialT,radialU,plainT,plainU]
  ring

theorem scaledSlack_two_upper (z a : ℝ) : scaledSlack 2 1 z a= -2*z*(2*a+z)*(a*z-1) := by
  rw [← polynomialSlack_eq]
  norm_num [polynomialSlack,radialT,radialU,plainT,plainU]
  ring

theorem scaledSlack_two_upper_nonneg {z a : ℝ} (hz : 0<z)
    (ha : -z/2≤a ∧ a≤0) : 0≤scaledSlack 2 1 z a := by
  rw [scaledSlack_two_upper]
  have h1 : 0≤2*a+z := by linarith [ha.1]
  have h2 : a*z-1≤0 := by nlinarith [mul_nonpos_of_nonpos_of_nonneg ha.2 hz.le]
  have hp : 0≤2*z*(2*a+z)*(-(a*z-1)) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hz.le) h1) (neg_nonneg.mpr h2)
  nlinarith

end
end polyak.Boundary.P1
