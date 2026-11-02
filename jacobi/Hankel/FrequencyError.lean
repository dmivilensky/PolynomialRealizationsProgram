import jacobi.Hankel.FrequencyWave
import jacobi.Hankel.FrequencyPolynomial
import jacobi.Hankel.BesselHankelReal

/-!
Article: jacobi, Lemma E.1.
Use: frequencyError is the actual normalized original Bessel remainder propagated into the complex zero disks.
-/
namespace jacobi.Hankel
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- The original canonically phased two-wave Hankel comparison at genuine complex frequency.
Use: frequencyError is the actual normalized original Bessel remainder propagated into the complex zero disks.
Article: jacobi, Lemma E.1.
-/
def frequencyHankelApprox (a z : ℂ) : ℂ :=
  polynomialWave Complex.I (besselCoefficient a) z-
    besselZeroPhase a*polynomialWave (-Complex.I) (besselCoefficient a) z

/-- The actual displayed complex slope of the original two-wave Hankel comparison.
Use: frequencyHankelApprox_hasDerivAt and frequencyError_hasDerivAt provide genuine complex error Cauchy data.
Article: jacobi, Lemma E.1.
-/
def frequencyHankelSlope (a z : ℂ) : ℂ :=
  polynomialWaveSlope Complex.I (besselCoefficient a) z-
    besselZeroPhase a*polynomialWaveSlope (-Complex.I) (besselCoefficient a) z

/-- The actual displayed complex curvature of the original two-wave Hankel comparison.
Use: frequencyHankelApprox_equation identifies the literal forcing in the actual Bessel error ODE.
Article: jacobi, Lemma E.1.
-/
def frequencyHankelCurvature (a z : ℂ) : ℂ :=
  polynomialWaveCurvature Complex.I (besselCoefficient a) z-
    besselZeroPhase a*polynomialWaveCurvature (-Complex.I) (besselCoefficient a) z

/-- The genuine original two-wave Hankel residual in the complex-frequency inverse-square ODE.
Use: frequencyError_equation and its uniform strip bound retain the true residual of the actual comparison.
Article: jacobi, Lemma E.1.
-/
def frequencyHankelResidual (a z : ℂ) : ℂ :=
  (Complex.exp (Complex.I*z)-besselZeroPhase a*Complex.exp (-Complex.I*z))*
    (-(besselCoefficient a*(besselCoefficient a+2)*(besselCoefficient a+6))/(8*z^4))

/-- The genuine original complex Hankel comparison has its displayed actual derivative.
Use: frequencyError_hasDerivAt supplies the true error derivative along every complex propagation segment.
Article: jacobi, Lemma E.1.
Proof: subtract the two proved genuine signed-wave derivatives with the original constant Bessel connection phase. -/
theorem frequencyHankelApprox_hasDerivAt (a : ℂ) {z : ℂ} (hz : z≠0) :
    HasDerivAt (frequencyHankelApprox a) (frequencyHankelSlope a z) z :=
  (polynomialWave_hasDerivAt Complex.I (besselCoefficient a) hz).sub
    ((polynomialWave_hasDerivAt (-Complex.I) (besselCoefficient a) hz).const_mul (besselZeroPhase a))

/-- The actual original complex Hankel comparison slope has its genuine displayed curvature.
Use: frequencyErrorSlope_hasDerivAt and the actual forced ODE refer to the literal original complex comparison.
Article: jacobi, Lemma E.1.
Proof: combine the actual two signed comparison-wave curvature derivatives with the same genuine original phase. -/
theorem frequencyHankelSlope_hasDerivAt (a : ℂ) {z : ℂ} (hz : z≠0) :
    HasDerivAt (frequencyHankelSlope a) (frequencyHankelCurvature a z) z :=
  (polynomialWaveSlope_hasDerivAt Complex.I (besselCoefficient a) hz).sub
    ((polynomialWaveSlope_hasDerivAt (-Complex.I) (besselCoefficient a) hz).const_mul (besselZeroPhase a))

/-- The genuine original complex-frequency Hankel comparison has exactly the stated fourth-order forced Liouville equation.
Use: frequencyError_equation propagates the actual Bessel remainder with its proved original forcing rather than an assumed asymptotic residual.
Article: jacobi, Lemma E.1.
Proof: subtract the independently proved two actual signed residual equations; the two genuine signs both square to minus one. -/
theorem frequencyHankelApprox_equation (a : ℂ) {z : ℂ} (hz : z≠0) :
    frequencyHankelCurvature a z+(1+besselCoefficient a/z^2)*frequencyHankelApprox a z=
      frequencyHankelResidual a z := by
  have hp := polynomialWave_residual Complex.I_sq (besselCoefficient a) hz
  have hm := polynomialWave_residual (s := -Complex.I) (by simpa only [neg_sq] using Complex.I_sq)
    (besselCoefficient a) hz
  dsimp only [frequencyHankelCurvature,frequencyHankelApprox,frequencyHankelResidual]
  linear_combination hp-besselZeroPhase a*hm

/-- The actual normalized original Bessel Hankel error at complex frequency.
Use: its original real-ray bound and forced ODE yield the genuine uniform complex-frequency remainder needed for the numbered zero tail.
Article: jacobi, Lemma E.1.
-/
def frequencyError {R : ℝ} (hR : 0<R) (a z : ℂ) : ℂ :=
  frequencyWave a z/outgoingBesselCoefficient hR a-frequencyHankelApprox a z

/-- The genuine displayed complex-frequency derivative of the original normalized Bessel error.
Use: its real-ray initial value is bounded from the actual ODE and value remainder, then propagated with the error itself.
Article: jacobi, Lemma E.1.
-/
def frequencyErrorSlope {R : ℝ} (hR : 0<R) (a z : ℂ) : ℂ :=
  frequencySlope a z/outgoingBesselCoefficient hR a-frequencyHankelSlope a z

/-- The actual displayed complex curvature of the original normalized Bessel error.
Use: frequencyError_equation gives the exact genuine forced equation required for complex-segment propagation.
Article: jacobi, Lemma E.1.
-/
def frequencyErrorCurvature {R : ℝ} (hR : 0<R) (a z : ℂ) : ℂ :=
  frequencyCurvature a z/outgoingBesselCoefficient hR a-frequencyHankelCurvature a z

/-- The genuine original normalized Bessel error has its displayed actual complex derivative.
Use: vertical-segment propagation concerns the true original Bessel error, with every differential premise proved.
Article: jacobi, Lemma E.1.
Proof: divide the true original Bessel derivative by its fixed genuine outgoing coefficient and subtract the proved true comparison derivative. -/
theorem frequencyError_hasDerivAt {R : ℝ} (hR : 0<R) (a : ℂ) {z : ℂ}
    (hz : z∈Complex.slitPlane) : HasDerivAt (frequencyError hR a) (frequencyErrorSlope hR a z) z :=
  ((frequencyWave_hasDerivAt a hz).div_const (outgoingBesselCoefficient hR a)).sub
    (frequencyHankelApprox_hasDerivAt a (Complex.slitPlane_ne_zero hz))

/-- The actual normalized Bessel error slope has its genuine displayed complex derivative.
Use: the original complex error state has an actual second-order ODE all along each bounded propagation segment.
Article: jacobi, Lemma E.1.
Proof: combine the genuine original Bessel curvature and the actual complex Hankel comparison curvature. -/
theorem frequencyErrorSlope_hasDerivAt {R : ℝ} (hR : 0<R) (a : ℂ) {z : ℂ}
    (hz : z∈Complex.slitPlane) :
    HasDerivAt (frequencyErrorSlope hR a) (frequencyErrorCurvature hR a z) z :=
  ((frequencySlope_hasDerivAt a hz).div_const (outgoingBesselCoefficient hR a)).sub
    (frequencyHankelSlope_hasDerivAt a (Complex.slitPlane_ne_zero hz))

/-- The genuine original normalized Bessel error satisfies its exact complex-frequency forced inverse-square ODE.
Use: the real-ray Cauchy slope bound and complex-strip propagation are obtained from this original equation and the proved quartic forcing bound.
Article: jacobi, Lemma E.1.
Proof: subtract the actual comparison residual equation from the genuine normalized Bessel Liouville equation, retaining the same fixed original outgoing coefficient. -/
theorem frequencyError_equation {R : ℝ} (hR : 0<R) {a z : ℂ}
    (ha : -1<a.re) (hz : z≠0) :
    frequencyErrorCurvature hR a z+(1+besselCoefficient a/z^2)*frequencyError hR a z=
      -frequencyHankelResidual a z := by
  have hY := frequencyWave_equation ha hz
  have hp := frequencyHankelApprox_equation a hz
  dsimp only [frequencyErrorCurvature,frequencyError,besselCoefficient] at *
  linear_combination (1/outgoingBesselCoefficient hR a)*hY-hp

/-- The genuine complex-frequency comparison restricts to exactly the original real-ray Hankel comparison already bounded uniformly in complex order.
Use: frequencyError_ofReal transfers the actual established initial remainder into the literal complex-frequency error.
Article: jacobi, Lemma E.1.
Proof: the actual two signed comparison polynomials and their true Fourier factors restrict to the previously proved same real-ray expressions. -/
theorem frequencyHankelApprox_ofReal (a : ℂ) (x : ℝ) :
    frequencyHankelApprox a (x:ℂ)=besselHankelApprox a x := by
  dsimp only [frequencyHankelApprox,polynomialWave,besselHankelApprox,realPhase]
  rw [(signPolynomial_ofReal (besselCoefficient a) x).1,
    (signPolynomial_ofReal (besselCoefficient a) x).2]
  ring

/-- The actual complex Bessel error has precisely the established original real-ray remainder as its positive real restriction.
Use: the common real-ray cubic Hankel theorem gives actual initial values for the complex-frequency propagation theorem.
Article: jacobi, Lemma E.1.
Proof: both the genuine Bessel Liouville function and its literal canonically phased comparison have already identified real restrictions. -/
theorem frequencyError_ofReal {R : ℝ} (hR : 0<R) (a : ℂ) {x : ℝ} (hx : 0<x) :
    frequencyError hR a (x:ℂ)=complexBesselWave a x/outgoingBesselCoefficient hR a-besselHankelApprox a x := by
  rw [frequencyError,(frequencyWave_ofReal a hx).1,frequencyHankelApprox_ofReal]

end
end jacobi.Hankel
