import jacobi.Jacobi.ShiftedPolynomial

/-!
Article: jacobi, Appendix C.1 (selected endpoint branch).
The genuine Jacobi polynomial has its exact value and first two derivatives
at the normalization endpoint. These are actual polynomial derivatives,
not coefficients of an unrelated formal series.
Source: the proved hypergeometric coefficient recurrence and polynomial differentiation.
Use: fixes the true endpoint value and starts the exact derivative recurrence.
-/
namespace jacobi.Jacobi
noncomputable section
open Polynomial Complex
set_option backward.isDefEq.respectTransparency false

/-- The genuine zeroth Jacobi hypergeometric coefficient is one.
Use: fixes the true endpoint value and starts the exact derivative recurrence.
Article: jacobi, Theorem 5.1.
Proof: each zeroth Pochhammer and the zeroth factorial is one. -/
theorem coefficient_zero (a b : ℂ) (n : ℕ) : coefficient a b n 0=1 := by
  simp [coefficient,ordinaryHypergeometricCoefficient]

/-- The actual shifted Jacobi polynomial has value one at zero.
Use: its logarithmic derivative is its ordinary derivative at the source's normalization endpoint.
Article: jacobi, Lemma 1.3.
Proof: polynomial evaluation at zero extracts its actual zeroth coefficient, already proved one. -/
theorem shiftedPolynomial_zero (a b : ℝ) (n : ℕ) : (shiftedPolynomial a b n).eval 0=1 := by
  rw [← coeff_zero_eq_eval_zero,shiftedPolynomial_coeff,coefficient_zero,Complex.one_re]

/-- The actual first shifted Jacobi derivative at zero has its exact finite formula.
Use: evaluates the finite scaled resolvent trace and proves its limit M=1/(2*(alpha+1)).
Article: jacobi, Section 3.2 (sharp comparison at U).
Proof: the recurrence at degree zero gives (alpha+1)*c_1=-n*(n+alpha+beta+1).
Polynomial differentiation extracts that same actual coefficient. -/
theorem shiftedPolynomial_derivative_zero {a b : ℝ} (ha : -1<a) (n : ℕ) :
    (shiftedPolynomial a b n).derivative.eval 0= -(n:ℝ)*(n+a+b+1)/(a+1) := by
  have h := real_coefficient_equation (b := b) ha n 0
  simp only [Nat.cast_zero,zero_add,add_zero,zero_sub,coefficient_zero,Complex.one_re,mul_one] at h
  rw [← coeff_zero_eq_eval_zero,coeff_derivative,shiftedPolynomial_coeff]
  norm_num only [Nat.cast_zero,zero_add,Nat.cast_one,mul_one]
  apply (eq_div_iff (show a+1≠0 by linarith)).mpr
  linear_combination h

/-- The actual second shifted Jacobi derivative at zero has its exact finite formula.
Use: evaluates the finite second Rayleigh sum via the derivative of the polynomial logarithmic derivative.
Article: jacobi, Section 3.2 (sharp comparison at U).
Proof: the recurrence at degree one expresses twice the second
coefficient in terms of the first. The already evaluated genuine first
derivative and the nonzero positive normalization factors give the formula. -/
theorem shiftedPolynomial_second_derivative_zero {a b : ℝ} (ha : -1<a) (n : ℕ) :
    (shiftedPolynomial a b n).derivative.derivative.eval 0=
      (n:ℝ)*(n-1)*(n+a+b+1)*(n+a+b+2)/((a+1)*(a+2)) := by
  -- All factors remain valid for degree zero and one, where the second derivative vanishes.
  have h := real_coefficient_equation (b := b) ha n 1
  have h1 := shiftedPolynomial_derivative_zero (b := b) ha n
  rw [← coeff_zero_eq_eval_zero,coeff_derivative,shiftedPolynomial_coeff] at h1
  norm_num only [Nat.cast_zero,zero_add,Nat.cast_one,mul_one] at h1
  rw [← coeff_zero_eq_eval_zero,coeff_derivative,coeff_derivative,shiftedPolynomial_coeff]
  norm_num only [Nat.cast_zero,zero_add,Nat.cast_one,Nat.cast_ofNat,mul_one,one_add_one_eq_two] at h ⊢
  rw [h1] at h
  have ha1 : a+1≠0 := by linarith
  have ha2 : a+2≠0 := by linarith
  apply (eq_div_iff (mul_ne_zero ha1 ha2)).mpr
  field_simp [ha1] at h
  linear_combination h

end
end jacobi.Jacobi
