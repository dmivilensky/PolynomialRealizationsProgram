import jacobi.Hankel.ResidualEquation
import jacobi.Hankel.TailInverse
import jacobi.Hankel.OrderRay

/-!
Article: jacobi, Lemma E.1.
Use: besselAmplitude_cubic gives the uniform complex-order Hankel remainder used to continue the original Bessel zero tail on a common disk.
-/
namespace jacobi.Hankel
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BoundedContinuousFunction
set_option backward.isDefEq.respectTransparency false

/-- The genuine outgoing Jost amplitude has its explicit cubic error from the actual Hankel polynomial for every complex coefficient in the original half-contraction domain.
Use: besselAmplitude_cubic gives the uniform complex-order Hankel remainder used to continue the original Bessel zero tail on a common disk.
Article: jacobi, Lemma E.1.
Proof: subtract the two true Volterra equations, use linearity of the same original integral operator, bound the actual residual forcing on the whole future ray by its exact quartic-tail integral, and apply the proved local half-contraction inverse estimate. -/
theorem outgoingAmplitude_cubic {R : ℝ} (hR : 0<R) {c : ℂ}
    (hc : ‖c‖/R≤1/2) {x : ℝ} (hx : R≤x) :
    ‖outgoingAmplitude (inverseSquare_integrable hR) c x-amplitudePolynomial c x‖≤
      ‖c*(c+2)*(c+6)‖/(12*x^3) := by
  -- The error is an actual difference of bounded continuous functions in the original fixed Banach space.
  let v := outgoingAmplitude (inverseSquare_integrable hR) c
  let p := polynomialRay hR c
  let f : OutgoingSpace := v-p
  have hxp : 0<x := hR.trans_le hx
  have hunit : ‖c‖*(∫ y : ℝ,‖inverseSquare R y‖)<1 := by
    rw [inverseSquare_norm_integral hR,← div_eq_mul_one_div]
    exact hc.trans_lt (by norm_num)
  have hcx : ‖c‖/x≤1/2 :=
    (div_le_div_of_nonneg_left (norm_nonneg c) hR hx).trans hc
  have he (y : ℝ) (hy : x≤y) :
      f y+c*outgoingIntegral (inverseSquare R) f y= -residualIntegral c y := by
    have hA := congrArg (fun w : OutgoingSpace => w y)
      (outgoingAmplitude_equation (inverseSquare_integrable hR) hunit)
    change v y=1-c*outgoingIntegral (inverseSquare R) v y at hA
    have hP := polynomialRay_volterra_residual hR c (hx.trans hy)
    have hL := congrArg (fun w : OutgoingSpace => w y)
      ((outgoingOperator (inverseSquare_integrable hR)).map_sub v p)
    change outgoingIntegral (inverseSquare R) f y=
      outgoingIntegral (inverseSquare R) v y-outgoingIntegral (inverseSquare R) p y at hL
    change v y-p y+c*outgoingIntegral (inverseSquare R) f y= -residualIntegral c y
    change p y+c*outgoingIntegral (inverseSquare R) p y-1=residualIntegral c y at hP
    rw [hL]
    linear_combination hA-hP
  have hM := tailInverse_bound hR hx hcx f
    (G := ‖c*(c+2)*(c+6)‖/(24*x^3)) (fun y hy => by
      rw [he y hy,norm_neg]
      apply (residualIntegral_bound c (hxp.trans_le hy)).trans
      gcongr)
  have hn := (norm_le_tailNorm f (x := x) le_rfl).trans hM
  change ‖v x-p x‖≤_ at hn
  change ‖v x-amplitudePolynomial c x‖≤_
  rw [show p x=amplitudePolynomial c x from polynomialRay_eq hR c hx] at hn
  exact hn.trans_eq (by ring)

/-- The actual outgoing Bessel amplitude has the genuine cubic Hankel remainder for every original complex order on its common far ray.
Use: boundedness of the actual quadratic coefficient on a complex-order disk makes this the uniform analytic outgoing expansion underlying the original tail-zero continuation in Lemma E.1.
Article: jacobi, Lemma E.1.
Proof: specialize the genuine solved-amplitude cubic estimate to the exact original Bessel coefficient c=1/4-alpha^2. -/
theorem besselAmplitude_cubic {R : ℝ} (hR : 0<R) {a : ℂ}
    (ha : ‖besselCoefficient a‖/R≤1/2) {x : ℝ} (hx : R≤x) :
    ‖besselAmplitude hR a x-amplitudePolynomial (besselCoefficient a) x‖≤
      ‖besselCoefficient a*(besselCoefficient a+2)*(besselCoefficient a+6)‖/(12*x^3) :=
  outgoingAmplitude_cubic hR ha hx

end
end jacobi.Hankel
