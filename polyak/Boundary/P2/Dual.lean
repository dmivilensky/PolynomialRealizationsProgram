import polyak.Boundary.P2.Atoms

/-!
Article: Lemma p2ids(b), the exact double square of the actual dual polynomial.
Use: positivity and the exact zero set hold on the whole frequency interval.
Proof: four checked scalar source identities are the coefficients of the quartic identity.
-/

namespace polyak.Boundary.P2
noncomputable section
open Spectral

/-- Article: the exact coefficient identity before division by the positive common denominator. -/
theorem double_square_identity {z : ℝ} (hz : z∈parameterInterval) (c : ℝ) :
    -((1-c^2-u z^2)*cubicAlpha (G z) (W z) c-
      2*u z*(1-c^2)*quadraticBeta (G z) (W z) c)=
      4*G z*(1-W z)*(atomPolynomial z c)^2 := by
  have h0 := double_square_coefficient0 hz
  have h1 := double_square_coefficient1 hz
  have h2 := double_square_coefficient2 hz
  have h3 := double_square_coefficient3 hz
  unfold cubicAlpha quadraticBeta atomPolynomial
  linear_combination h0+c*h1+c^2*h2+c^3*h3

/-- Article: W and 1−W are strictly positive on the full source interval J. -/
theorem weight_bounds {z : ℝ} (hz : z∈parameterInterval) : 0<W z ∧ W z<1 := by
  have hl := W_lower_positive z hz
  have hu := W_upper_positive z hz
  constructor <;> linarith

/-- Article: the actual P₂ dual simplex vector. -/
def dualWeights (z : ℝ) (hz : z∈parameterInterval) : DualWeights :=
  weights23 (W z) (weight_bounds hz).1.le (weight_bounds hz).2.le

/-- Article: the actual parameter satisfies G>1 throughout J. -/
theorem one_lt_G {z : ℝ} (hz : z∈parameterInterval) : 1<G z := by
  have hl := G_lower_positive z hz
  linarith

/-- Article: Q is the positive multiple of the double square of the atom polynomial. -/
theorem dualPolynomial_factor_p2 {z : ℝ} (hz : z∈parameterInterval) (c : Frequency) :
    (dualPolynomial (dualWeights z hz) (u z) (G z)).eval (c : ℝ)=
      (4*(1-W z)/(4*G z^2-1))*(atomPolynomial z c)^2 := by
  have hg := one_lt_G hz
  have hg0 : G z≠0 := by linarith
  have hd : 4*G z^2-1≠0 := by nlinarith
  have hd' : G z^2*4-1≠0 := by nlinarith
  have hgap : G z-(c : ℝ)≠0 := by linarith [c.property.2]
  have he := dualSymbol_weights23_factor (W z) (weight_bounds hz).1.le (weight_bounds hz).2.le hg.le (u z) c
  change dualSymbol (dualWeights z hz) (u z) (G z) c=_ at he
  rw [dualPolynomial_factor _ _ hg.le] at he
  have hsq := double_square_identity hz c
  have hnum : (1-(c : ℝ)^2-u z^2)*cubicAlpha (G z) (W z) c-
      2*u z*(1-(c : ℝ)^2)*quadraticBeta (G z) (W z) c =
      -4*G z*(1-W z)*(atomPolynomial z c)^2 := by linarith
  rw [hnum] at he
  have hr : (G z-c)*(-4*G z*(1-W z)*(atomPolynomial z c)^2)/(G z*(4*G z^2-1))=
      -(G z-c)*((4*(1-W z)/(4*G z^2-1))*(atomPolynomial z c)^2) := by
    field_simp [hg0,hd,hd']
  rw [hr] at he
  exact mul_left_cancel₀ (neg_ne_zero.mpr hgap) he

/-- Article: nonnegativity of the actual P₂ dual polynomial everywhere on [-1,1]. -/
theorem dualPolynomial_nonneg {z : ℝ} (hz : z∈parameterInterval) (c : Frequency) :
    0 ≤ (dualPolynomial (dualWeights z hz) (u z) (G z)).eval (c : ℝ) := by
  rw [dualPolynomial_factor_p2 hz]
  have hg := one_lt_G hz
  have hw := (weight_bounds hz).2
  exact mul_nonneg (div_nonneg (by linarith) (by nlinarith)) (sq_nonneg _)

/-- Article: the zeros of the actual dual polynomial are exactly its two selected interior atoms. -/
theorem dualPolynomial_zero_iff {z : ℝ} (hz : z∈parameterInterval) (c : Frequency) :
    (dualPolynomial (dualWeights z hz) (u z) (G z)).eval (c : ℝ)=0 ↔ (c : ℝ)=x z ∨ (c : ℝ)=y z := by
  rw [dualPolynomial_factor_p2 hz]
  have hg := one_lt_G hz
  have hw := (weight_bounds hz).2
  have hp : 0 < 4*(1-W z)/(4*G z^2-1) := div_pos (by linarith) (by nlinarith)
  rw [mul_eq_zero,or_iff_right (ne_of_gt hp),sq_eq_zero_iff,atomPolynomial_factor hz,mul_eq_zero]
  simp only [sub_eq_zero]

end
end polyak.Boundary.P2
