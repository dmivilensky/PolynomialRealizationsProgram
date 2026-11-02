import jacobi.Hankel.IncomingAmplitude
import jacobi.Hankel.CubicRemainder

/-!
Article: jacobi, Lemma E.1.
Use: incomingAmplitude_cubic and the original Bessel decomposition give a true two-sided-wave cubic Hankel approximation at complex order.
-/
namespace jacobi.Hankel
noncomputable section
open scoped BoundedContinuousFunction
set_option backward.isDefEq.respectTransparency false

/-- The original incoming Hankel amplitude through its inverse-square term.
Use: incomingAmplitude_cubic and the original Bessel decomposition give a true two-sided-wave cubic Hankel approximation at complex order.
Article: jacobi, Lemma E.1.
-/
def incomingPolynomial (c : ℂ) (x : ℝ) : ℂ :=
  1+Complex.I*c/(2*(x:ℂ))-c*(c+2)/(8*(x:ℂ)^2)

/-- Conjugation at conjugate coefficient identifies the genuine outgoing comparison polynomial with the original incoming polynomial.
Use: incomingAmplitude_cubic transfers the actual solved outgoing error without assuming an incoming asymptotic expansion.
Article: jacobi, Lemma E.1.
Proof: conjugate the actual rational polynomial, use the real spatial coordinate and the opposite imaginary unit, and cancel the true coefficient conjugations. -/
theorem amplitudePolynomial_star (c : ℂ) (x : ℝ) :
    star (amplitudePolynomial (star c) x)=incomingPolynomial c x := by
  simp [amplitudePolynomial,incomingPolynomial]
  ring

/-- The genuine incoming Bessel amplitude has its actual explicit cubic Hankel remainder for every original complex order in the common far-ray domain.
Use: bessel_realRay_hankel combines the two actual Jost errors in the original Bessel solution, retaining the original complex coefficient and exact canonical phase.
Article: jacobi, Lemma E.1.
Proof: apply the already proved actual outgoing cubic estimate at conjugate order, conjugate the actual amplitude and comparison polynomial, and use norm invariance of the true residual coefficient under complex conjugation. -/
theorem incomingAmplitude_cubic {R : ℝ} (hR : 0<R) {a : ℂ}
    (ha : ‖besselCoefficient a‖/R≤1/2) {x : ℝ} (hx : R≤x) :
    ‖incomingAmplitude hR a x-incomingPolynomial (besselCoefficient a) x‖≤
      ‖besselCoefficient a*(besselCoefficient a+2)*(besselCoefficient a+6)‖/(12*x^3) := by
  -- The incoming estimate is for the actual conjugated solution and its true residual, not for an independently postulated expansion.
  have hs : ‖besselCoefficient (star a)‖/R≤1/2 := by
    simpa only [besselCoefficient_star,norm_star] using ha
  have h := besselAmplitude_cubic hR hs hx
  rw [besselCoefficient_star] at h
  have hp : star (besselCoefficient a)*(star (besselCoefficient a)+2)*(star (besselCoefficient a)+6)=
      star (besselCoefficient a*(besselCoefficient a+2)*(besselCoefficient a+6)) := by simp
  rw [hp,norm_star] at h
  change ‖star (besselAmplitude hR (star a) x)-incomingPolynomial (besselCoefficient a) x‖≤_
  rw [← amplitudePolynomial_star,← star_sub,norm_star]
  exact h

end
end jacobi.Hankel
