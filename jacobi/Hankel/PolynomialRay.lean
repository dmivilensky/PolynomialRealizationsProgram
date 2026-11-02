import jacobi.Hankel.AsymptoticPolynomial

/-!
Article: jacobi, Lemma E.1.
Use: polynomialRay is a genuine element of the same bounded-continuous Banach space as the original outgoing amplitude.
-/
namespace jacobi.Hankel
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BoundedContinuousFunction
set_option backward.isDefEq.respectTransparency false

/-- The actual reciprocal coordinate frozen only below the original fixed positive outgoing cutoff.
Use: polynomialRay is a genuine element of the same bounded-continuous Banach space as the original outgoing amplitude.
Article: jacobi, Lemma E.1.
-/
def reciprocalRay {R : ℝ} (hR : 0<R) : OutgoingSpace :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun x : ℝ => ((max R x)⁻¹:ℝ))
    (Complex.continuous_ofReal.comp ((continuous_const.max continuous_id).inv₀
      (fun x => (hR.trans_le (le_max_left R x)).ne'))) (1/R)
    (fun x => by
      rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg
        (inv_nonneg.mpr ((hR.trans_le (le_max_left R x)).le)),one_div]
      exact inv_anti₀ hR (le_max_left R x))

/-- The bounded continuous extension of the genuine outgoing Hankel polynomial on the original fixed ray.
Use: its actual difference from the original Jost amplitude lies in the same fixed Banach space, and the proved local inverse estimates its literal cubic residual.
Article: jacobi, Lemma E.1.
-/
def polynomialRay {R : ℝ} (hR : 0<R) (c : ℂ) : OutgoingSpace :=
  1-(Complex.I*c/2) • reciprocalRay hR-(c*(c+2)/8) • (reciprocalRay hR)^2

/-- Above the original cutoff the actual bounded extension is exactly the displayed outgoing Hankel polynomial.
Use: the original polynomial's genuine derivatives, residual and normalization at infinity apply to this same comparison in the solved Volterra equation.
Article: jacobi, Lemma E.1.
Proof: evaluate the bounded-function algebra pointwise, use max(R,x)=x, and simplify the original reciprocal denominators. -/
theorem polynomialRay_eq {R : ℝ} (hR : 0<R) (c : ℂ) {x : ℝ} (hx : R≤x) :
    polynomialRay hR c x=amplitudePolynomial c x := by
  change 1-(Complex.I*c/2)*(((max R x)⁻¹:ℝ):ℂ)-
    (c*(c+2)/8)*((((max R x)⁻¹:ℝ):ℂ))^2=amplitudePolynomial c x
  rw [max_eq_right hx,Complex.ofReal_inv]
  unfold amplitudePolynomial
  simp only [div_eq_mul_inv,mul_inv_rev,inv_pow]
  ring

/-- The original real reciprocal coordinate tends to zero at positive infinity, also as a genuine complex-valued map.
Use: the outgoing asymptotic polynomial and its true slope have the endpoint limits required by the actual improper residual primitive.
Article: jacobi, Lemma E.1.
Proof: compose the community real reciprocal limit with the continuous real inclusion in the complex plane. -/
theorem complex_reciprocal_limit :
    Tendsto (fun x : ℝ => (x:ℂ)⁻¹) atTop (𝓝 0) := by
  simpa only [Function.comp_def,Complex.ofReal_inv,Complex.ofReal_zero] using
    (Complex.continuous_ofReal.tendsto (0:ℝ)).comp tendsto_inv_atTop_zero

/-- The actual outgoing Hankel polynomial tends to its original normalization one at infinity.
Use: the genuine Volterra residual primitive has its actual boundary value at infinity, rather than an assumed asymptotic endpoint.
Article: jacobi, Lemma E.1.
Proof: rewrite the displayed rational polynomial in the reciprocal coordinate, whose genuine limit is zero. -/
theorem amplitudePolynomial_limit (c : ℂ) :
    Tendsto (amplitudePolynomial c) atTop (𝓝 1) := by
  have h := ((tendsto_const_nhds (x := (1:ℂ))).sub (complex_reciprocal_limit.const_mul (Complex.I*c/2))).sub
    ((complex_reciprocal_limit.pow 2).const_mul (c*(c+2)/8))
  convert! h using 1
  · funext x
    simp only [amplitudePolynomial,div_eq_mul_inv,mul_inv_rev,inv_pow]
    ring
  · simp

/-- The genuine first derivative of the outgoing Hankel polynomial tends to zero at infinity.
Use: together with amplitudePolynomial_limit and the true bounded oscillatory kernel, discharges the upper endpoint of the actual residual primitive.
Article: jacobi, Lemma E.1.
Proof: both actual slope terms are fixed multiples of positive powers of the reciprocal coordinate, whose genuine limit is zero. -/
theorem amplitudePolynomialSlope_limit (c : ℂ) :
    Tendsto (amplitudePolynomialSlope c) atTop (𝓝 0) := by
  have h := ((complex_reciprocal_limit.pow 2).const_mul (Complex.I*c/2)).add
    ((complex_reciprocal_limit.pow 3).const_mul (c*(c+2)/4))
  convert! h using 1
  · funext x
    simp only [amplitudePolynomialSlope,div_eq_mul_inv,mul_inv_rev,inv_pow]
    ring
  · simp

end
end jacobi.Hankel
