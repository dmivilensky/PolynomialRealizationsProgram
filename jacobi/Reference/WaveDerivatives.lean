import jacobi.Reference.Wave

/-!
Article: jacobi, Appendix C.1 (negative-energy bounds).
The actual source reference function has two genuine spatial derivatives
at every physical interior point for arbitrary complex frequency. The
hypergeometric factor and both differentiated factors are evaluated
inside the actual community convergence disk.
Use: computes the true reference second spatial derivative under the actual source substitution.
-/
namespace jacobi.Reference
noncomputable section
open Real Set Complex
set_option backward.isDefEq.respectTransparency false

/-- The exact second derivative of the physical cosine coordinate.
Use: computes the true reference second spatial derivative under the actual source substitution.
Article: jacobi, Appendix C.1 (negative-energy bounds).
-/
def coordinateAcceleration (t : ℝ) : ℝ := Real.pi^2*Real.cos (Real.pi*t)/2

/-- The physical coordinate slope has the actual ordinary derivative given by its literal acceleration.
Use: the reference Gauss-to-Schrodinger substitution concerns actual second derivatives.
Article: jacobi, Appendix C.1 (negative-energy bounds).
Proof: differentiate the literal sine Jacobian using the community chain rule. -/
theorem coordinateSlope_hasDerivAt (t : ℝ) : HasDerivAt coordinateSlope (coordinateAcceleration t) t := by
  convert (((Real.hasDerivAt_sin (Real.pi*t)).comp t ((hasDerivAt_id t).const_mul Real.pi)).const_mul Real.pi).div_const 2 using 1
  · rfl
  · dsimp [coordinateAcceleration]
    ring

/-- The explicit original first spatial derivative of the complex reference solution.
Use: fixes the true complex midpoint boundary function and transformed reference derivative.
Article: jacobi, Appendix C.1 (negative-energy bounds).
-/
def waveSlope (a : ℝ) (omega : ℂ) (t : ℝ) : ℂ :=
  (weight a t:ℂ)*((weightLogSlope a t:ℂ)*waveCore a omega (coordinate t:ℂ)+
    (coordinateSlope t:ℂ)*deriv (waveCore a omega) (coordinate t:ℂ))

/-- The explicit original second spatial derivative of the complex reference solution.
Use: proves the original reference Schrodinger equation for every complex spectral parameter.
Article: jacobi, Appendix C.1 (negative-energy bounds).
-/
def waveAcceleration (a : ℝ) (omega : ℂ) (t : ℝ) : ℂ :=
  (weight a t:ℂ)*(((weightLogAcceleration a t:ℂ)+(weightLogSlope a t:ℂ)^2)*waveCore a omega (coordinate t:ℂ)+
    (2*(weightLogSlope a t:ℂ)*(coordinateSlope t:ℂ)+(coordinateAcceleration t:ℂ))*deriv (waveCore a omega) (coordinate t:ℂ)+
    (coordinateSlope t:ℂ)^2*deriv (deriv (waveCore a omega)) (coordinate t:ℂ))

/-- The original complex reference slope is the actual ordinary spatial derivative throughout the physical interval.
Use: the reference and transformed midpoint boundary data use genuine derivatives of the source function.
Article: jacobi, Appendix C.1 (negative-energy bounds).
Proof: differentiate the actual positive sine-power prefactor and the genuine analytic hypergeometric factor at the physical coordinate. -/
theorem wave_hasDerivAt (a : ℝ) (omega : ℂ) {t : ℝ} (ht : t∈Ioo 0 1) :
    HasDerivAt (wave a omega) (waveSlope a omega t) t := by
  -- The real-to-complex casts preserve the actual physical spatial derivative.
  have hw := (weight_hasDerivAt a ht).ofReal_comp
  have hh := ((waveCore_analytic a omega ht).differentiableAt.hasDerivAt).comp t (coordinate_hasDerivAt t).ofReal_comp
  convert hw.mul hh using 1
  · rfl
  · dsimp [waveSlope]
    push_cast
    ring

/-- The original complex reference acceleration is the actual ordinary derivative of its actual slope.
Use: establishes the genuine second-order reference equation at every complex frequency with no regularity premise.
Article: jacobi, Lemma C.1.
Proof: the analytic actual hypergeometric function has an analytic
derivative. Compose both derivatives with the genuine physical coordinate
and differentiate the explicit first spatial derivative by product rules. -/
theorem waveSlope_hasDerivAt (a : ℝ) (omega : ℂ) {t : ℝ} (ht : t∈Ioo 0 1) :
    HasDerivAt (waveSlope a omega) (waveAcceleration a omega t) t := by
  -- Every differentiated constituent is the actual original source function or its genuine ordinary derivative.
  have hw := (weight_hasDerivAt a ht).ofReal_comp
  have hL := (weightLogSlope_hasDerivAt a ht).ofReal_comp
  have hx := (coordinate_hasDerivAt t).ofReal_comp
  have hx' := (coordinateSlope_hasDerivAt t).ofReal_comp
  have hh := ((waveCore_analytic a omega ht).differentiableAt.hasDerivAt).comp t hx
  have hh' := ((waveCore_analytic a omega ht).deriv.differentiableAt.hasDerivAt).comp t hx
  convert hw.mul ((hL.mul hh).add (hx'.mul hh')) using 1
  · rfl
  · dsimp [waveAcceleration]
    push_cast
    ring

end
end jacobi.Reference
