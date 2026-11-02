import jacobi.Hankel.OrderRay

/-!
Article: jacobi, Lemma E.1.
Use: amplitudePolynomial_residual computes its genuine ODE error; the local outgoing inverse then preserves the required cubic amplitude error.
-/
namespace jacobi.Hankel
noncomputable section
open Complex
set_option backward.isDefEq.respectTransparency false

/-- The original outgoing asymptotic amplitude through the inverse-square term.
Use: amplitudePolynomial_residual computes its genuine ODE error; the local outgoing inverse then preserves the required cubic amplitude error.
Article: jacobi, Lemma E.1.
-/
def amplitudePolynomial (c : ℂ) (x : ℝ) : ℂ :=
  1-I*c/(2*(x:ℂ))-c*(c+2)/(8*(x:ℂ)^2)

/-- The actual first derivative of the outgoing asymptotic amplitude.
Use: amplitudePolynomial_hasDerivAt and the exact residual primitive give the original Volterra residual identity.
Article: jacobi, Lemma E.1.
-/
def amplitudePolynomialSlope (c : ℂ) (x : ℝ) : ℂ :=
  I*c/(2*(x:ℂ)^2)+c*(c+2)/(4*(x:ℂ)^3)

/-- The actual second derivative of the outgoing asymptotic amplitude.
Use: amplitudePolynomial_residual identifies its exact source under the original inverse-square Liouville operator.
Article: jacobi, Lemma E.1.
-/
def amplitudePolynomialCurvature (c : ℂ) (x : ℝ) : ℂ :=
  -I*c/(x:ℂ)^3-3*c*(c+2)/(4*(x:ℂ)^4)

/-- The explicit outgoing asymptotic amplitude has its stated genuine real spatial derivative away from zero.
Use: its residual is integrated by the actual improper fundamental theorem of calculus, so the asymptotic calculation refers to genuine derivatives.
Article: jacobi, Lemma E.1.
Proof: apply the complex-valued real quotient and power derivative rules to the actual displayed polynomial and simplify its nonzero denominator algebra. -/
theorem amplitudePolynomial_hasDerivAt (c : ℂ) {x : ℝ} (hx : x≠0) :
    HasDerivAt (amplitudePolynomial c) (amplitudePolynomialSlope c x) x := by
  -- All differentiations are away from the original singular endpoint.
  have hz : (x:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hx
  have hd := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt x (hasDerivAt_id x)
  have hp := (hasDerivAt_const x (1:ℂ)).sub
    ((hasDerivAt_const x (I*c)).div (hd.const_mul 2) (mul_ne_zero (by norm_num) hz))
  convert hp.sub ((hasDerivAt_const x (c*(c+2))).div ((hd.pow 2).const_mul 8)
    (mul_ne_zero (by norm_num) (pow_ne_zero 2 hz))) using 1
  · rfl
  · simp only [amplitudePolynomialSlope,Function.comp_def,id_eq,Complex.ofRealCLM_apply,
      ofReal_one,zero_mul,zero_sub,mul_one,Pi.pow_apply]
    field_simp
    ring

/-- The actual slope of the outgoing asymptotic polynomial has its stated genuine derivative away from zero.
Use: amplitudePolynomial_residual is the true second-order Liouville error of the original approximation.
Article: jacobi, Lemma E.1.
Proof: differentiate its two actual inverse powers by the quotient rule and simplify the original nonzero complex denominator. -/
theorem amplitudePolynomialSlope_hasDerivAt (c : ℂ) {x : ℝ} (hx : x≠0) :
    HasDerivAt (amplitudePolynomialSlope c) (amplitudePolynomialCurvature c x) x := by
  -- The complex coefficient is fixed while the original real spatial variable is differentiated.
  have hz : (x:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hx
  have hd := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt x (hasDerivAt_id x)
  convert ((hasDerivAt_const x (I*c)).div ((hd.pow 2).const_mul 2)
    (mul_ne_zero (by norm_num) (pow_ne_zero 2 hz))).add
    ((hasDerivAt_const x (c*(c+2))).div ((hd.pow 3).const_mul 4)
      (mul_ne_zero (by norm_num) (pow_ne_zero 3 hz))) using 1
  · rfl
  · simp only [amplitudePolynomialCurvature,Function.comp_def,id_eq,Complex.ofRealCLM_apply,
      ofReal_one,zero_mul,zero_sub,mul_one,Pi.pow_apply]
    field_simp
    ring

/-- The genuine outgoing Hankel polynomial has exactly the stated fourth-order Liouville residual for every complex coefficient.
Use: its original residual has integrable tail O(x^-3); tailInverse_bound then produces the uniform cubic error needed for sigma_k-tau_k=O(k^-2).
Article: jacobi, Lemma E.1.
Proof: substitute the actual polynomial and its proved two spatial derivatives into the original Liouville amplitude operator and clear its nonzero denominator. -/
theorem amplitudePolynomial_residual (c : ℂ) {x : ℝ} (hx : x≠0) :
    amplitudePolynomialCurvature c x+2*I*amplitudePolynomialSlope c x+
      c/(x:ℂ)^2*amplitudePolynomial c x = -c*(c+2)*(c+6)/(8*(x:ℂ)^4) := by
  have hz : (x:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hx
  unfold amplitudePolynomial amplitudePolynomialSlope amplitudePolynomialCurvature
  field_simp
  ring_nf
  norm_num [pow_succ]

end
end jacobi.Hankel
