import jacobi.Hankel.OrderRay
import jacobi.Hankel.IntegralDifferential
import jacobi.Hankel.PotentialRegularity

/-!
Article: jacobi, Lemma E.1.
Use: besselAmplitude_hasDerivAt and besselAmplitudeSlope_hasDerivAt establish the actual outgoing Liouville equation needed for the common complex-order Hankel expansion.
-/
namespace jacobi.Hankel
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BoundedContinuousFunction
set_option backward.isDefEq.respectTransparency false

/-- The true spatial slope of the original outgoing normalized Bessel amplitude.
Use: besselAmplitude_hasDerivAt and besselAmplitudeSlope_hasDerivAt establish the actual outgoing Liouville equation needed for the common complex-order Hankel expansion.
Article: jacobi, Lemma E.1.
-/
def besselAmplitudeSlope {R : ℝ} (hR : 0<R) (a : ℂ) (x : ℝ) : ℂ :=
  -besselCoefficient a*outgoingSlope (inverseSquare R) (besselAmplitude hR a) x

/-- The original analytic Banach-inverse Bessel amplitude has its stated true spatial derivative on the genuine outgoing ray.
Use: its original Volterra inverse and its subsequent ODE, Wronskian and Bessel asymptotic comparisons all concern the same actually constructed solution.
Article: jacobi, Lemma E.1.
Proof: evaluate the genuine solved integral equation as a function identity and differentiate the true outgoing integral using the independently proved FTC and inverse-square continuity. -/
theorem besselAmplitude_hasDerivAt {R : ℝ} (hR : 0<R) {a : ℂ}
    (ha : ‖besselCoefficient a‖/R<1) {x : ℝ} (hx : R<x) :
    HasDerivAt (fun y : ℝ => besselAmplitude hR a y) (besselAmplitudeSlope hR a x) x := by
  -- Differentiate the literal solved integral equation, with its genuine local continuity premise discharged.
  have hc : ‖besselCoefficient a‖*(∫ y : ℝ,‖inverseSquare R y‖)<1 := by
    rwa [inverseSquare_norm_integral hR,← div_eq_mul_one_div]
  have he : (fun y : ℝ => besselAmplitude hR a y)=
      fun y => 1-besselCoefficient a*outgoingIntegral (inverseSquare R) (besselAmplitude hR a) y := by
    funext y
    exact congrArg (fun f : OutgoingSpace => f y)
      (outgoingAmplitude_equation (inverseSquare_integrable hR) hc)
  rw [he]
  convert! (hasDerivAt_const x (1:ℂ)).sub
    ((outgoingIntegral_hasDerivAt (inverseSquare_integrable hR) (inverseSquare_measurable R)
      (besselAmplitude hR a) (inverseSquare_continuousAt hR hx)).const_mul (besselCoefficient a)) using 1
  simp only [besselAmplitudeSlope,zero_sub,neg_mul]

/-- The true original outgoing Bessel amplitude slope has the original Liouville second derivative on the genuine fixed ray.
Use: the actual holomorphic complex-order outgoing solution satisfies v''+2iv'+c*v/x^2=0, as required to compare it to the original Bessel solution and obtain the uniform high-index zero tail.
Article: jacobi, Lemma E.1.
Proof: use the proved outgoing Fourier derivative equation and the actual inverse-square value, then expand the original slope definition. -/
theorem besselAmplitudeSlope_hasDerivAt {R : ℝ} (hR : 0<R) (a : ℂ)
    {x : ℝ} (hx : R<x) :
    HasDerivAt (besselAmplitudeSlope hR a)
      (-2*Complex.I*besselAmplitudeSlope hR a x-
        besselCoefficient a/(x:ℂ)^2*besselAmplitude hR a x) x := by
  -- The ODE follows from the true Fourier tails for the actual constructed amplitude, not from formal inverse differentiation.
  convert! (outgoingSlope_hasDerivAt (inverseSquare_integrable hR) (inverseSquare_measurable R)
    (besselAmplitude hR a) (inverseSquare_continuousAt hR hx)).const_mul (-besselCoefficient a) using 1
  rw [inverseSquare_eq hx]
  push_cast
  dsimp only [besselAmplitudeSlope]
  ring

end
end jacobi.Hankel
