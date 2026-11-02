import jacobi.Hankel.ResidualPrimitive
import jacobi.Hankel.ResidualBound
import jacobi.Hankel.PotentialRegularity

/-!
Article: jacobi, Lemma E.1.
Use: polynomialRay_volterra_residual identifies the original full-line bounded operator with its literal improper future-ray integral, without changing its potential or amplitude.
-/
namespace jacobi.Hankel
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BoundedContinuousFunction
set_option backward.isDefEq.respectTransparency false

/-- The actual outgoing kernel source vanishes outside its genuine future integration ray.
Use: polynomialRay_volterra_residual identifies the original full-line bounded operator with its literal improper future-ray integral, without changing its potential or amplitude.
Article: jacobi, Lemma E.1.
Proof: below or on the true diagonal y=x the original clipped sine kernel is exactly zero. -/
theorem outgoingIntegral_eq_tail (m : ℝ → ℝ) (f : OutgoingSpace) (x : ℝ) :
    outgoingIntegral m f x=(∫ y in Ioi x,outgoingKernel (y-x)*((m y:ℂ)*f y)) := by
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro y hy
  rw [outgoingKernel_zero (sub_nonpos.mpr (not_lt.mp hy)),zero_mul]

/-- The actual bounded outgoing Hankel polynomial satisfies exactly the genuine original Volterra equation with its true fourth-order residual forcing.
Use: outgoingAmplitude_cubic subtracts this proved identity from the actual analytic Jost inverse equation and applies the genuine local inverse estimate.
Article: jacobi, Lemma E.1.
Proof: the true polynomial Green primitive evaluates its Liouville-source integral. Its exact ODE residual splits this original convergent integral into the genuine fourth-order forcing and the actual potential-amplitude term. The causal-support identity identifies that latter integral with the original bounded Volterra operator. -/
theorem polynomialRay_volterra_residual {R : ℝ} (hR : 0<R) (c : ℂ) {x : ℝ} (hx : R≤x) :
    polynomialRay hR c x+c*outgoingIntegral (inverseSquare R) (polynomialRay hR c) x-1=
      residualIntegral c x := by
  -- Split only the original integrals whose absolute convergence has already been proved independently.
  have hxp : 0<x := hR.trans_le hx
  have hi := (outgoingIntegrand_integrable (inverseSquare_integrable hR) (polynomialRay hR c) x).integrableOn (s := Ioi x)
  have he (y : ℝ) (hy : y∈Ioi x) :
      outgoingKernel (y-x)*(amplitudePolynomialCurvature c y+2*Complex.I*amplitudePolynomialSlope c y)=
      outgoingKernel (y-x)*amplitudeResidual c y-
        c*(outgoingKernel (y-x)*((inverseSquare R y:ℂ)*polynomialRay hR c y)) := by
    rw [polynomialRay_eq hR c (hx.trans hy.le),inverseSquare_eq (hx.trans_lt hy)]
    push_cast
    have hr := amplitudePolynomial_residual c (hxp.trans hy).ne'
    dsimp only [amplitudeResidual]
    linear_combination outgoingKernel (y-x)*hr
  have hm : residualIntegral c x-c*outgoingIntegral (inverseSquare R) (polynomialRay hR c) x=
      amplitudePolynomial c x-1 := calc
    _ = (∫ y in Ioi x,outgoingKernel (y-x)*amplitudeResidual c y)-
        (∫ y in Ioi x,c*(outgoingKernel (y-x)*((inverseSquare R y:ℂ)*polynomialRay hR c y))) := by
      rw [integral_const_mul,← outgoingIntegral_eq_tail]
      rfl
    _ = ∫ y in Ioi x,outgoingKernel (y-x)*amplitudeResidual c y-
        c*(outgoingKernel (y-x)*((inverseSquare R y:ℂ)*polynomialRay hR c y)) :=
      (integral_sub (residualIntegrand_integrable c hxp) (hi.const_mul c)).symm
    _ = ∫ y in Ioi x,outgoingKernel (y-x)*(amplitudePolynomialCurvature c y+
        2*Complex.I*amplitudePolynomialSlope c y) :=
      setIntegral_congr_fun measurableSet_Ioi (fun y hy => (he y hy).symm)
    _ = _ := polynomial_outgoing_identity c hxp
  rw [polynomialRay_eq hR c hx]
  linear_combination -hm

end
end jacobi.Hankel
