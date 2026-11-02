import jacobi.Hankel.IncomingRemainder

/-!
Article: jacobi, Lemma E.1.
Use: polynomialWave packages the outgoing sign +i and incoming sign -i in one actual complex-frequency comparison.
-/
namespace jacobi.Hankel
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- The original signed Hankel amplitude polynomial at genuine complex frequency.
Use: polynomialWave packages the outgoing sign +i and incoming sign -i in one actual complex-frequency comparison.
Article: jacobi, Lemma E.1.
-/
def signPolynomial (s c z : ℂ) : ℂ := 1-s*c/(2*z)-c*(c+2)/(8*z^2)

/-- The actual displayed first derivative of the signed complex Hankel amplitude.
Use: signPolynomial_hasDerivAt and polynomialWave_hasDerivAt give the true complex Cauchy comparison data.
Article: jacobi, Lemma E.1.
-/
def signPolynomialSlope (s c z : ℂ) : ℂ := s*c/(2*z^2)+c*(c+2)/(4*z^3)

/-- The actual displayed second derivative of the signed complex Hankel amplitude.
Use: signPolynomial_residual proves the exact original fourth-order complex-frequency ODE error.
Article: jacobi, Lemma E.1.
-/
def signPolynomialCurvature (s c z : ℂ) : ℂ := -s*c/z^3-3*c*(c+2)/(4*z^4)

/-- The genuine complex signed Hankel amplitude has its displayed derivative at every nonzero frequency.
Use: polynomialWave_hasDerivAt differentiates the actual comparison rather than a formal asymptotic series.
Article: jacobi, Lemma E.1.
Proof: use the complex quotient and power rules for the actual two rational terms and clear the original nonzero spatial denominator. -/
theorem signPolynomial_hasDerivAt (s c : ℂ) {z : ℂ} (hz : z≠0) :
    HasDerivAt (signPolynomial s c) (signPolynomialSlope s c z) z := by
  -- All denominator cancellations refer to the actual nonzero complex frequency.
  have h := (hasDerivAt_const z (1:ℂ)).sub
    ((hasDerivAt_const z (s*c)).div ((hasDerivAt_id z).const_mul 2) (mul_ne_zero (by norm_num) hz))
  convert! h.sub ((hasDerivAt_const z (c*(c+2))).div (((hasDerivAt_id z).pow 2).const_mul 8)
    (mul_ne_zero (by norm_num) (pow_ne_zero 2 hz))) using 1
  simp only [signPolynomialSlope,Pi.pow_apply,id_eq,Nat.reduceSub,pow_one,mul_one,zero_mul,zero_sub]
  field_simp
  ring

/-- The genuine signed amplitude slope has the displayed actual complex derivative.
Use: signPolynomial_residual is the true curvature error of the original rational approximation.
Article: jacobi, Lemma E.1.
Proof: differentiate its original inverse-square and inverse-cube terms with their actual nonzero frequency denominators. -/
theorem signPolynomialSlope_hasDerivAt (s c : ℂ) {z : ℂ} (hz : z≠0) :
    HasDerivAt (signPolynomialSlope s c) (signPolynomialCurvature s c z) z := by
  convert! ((hasDerivAt_const z (s*c)).div (((hasDerivAt_id z).pow 2).const_mul 2)
    (mul_ne_zero (by norm_num) (pow_ne_zero 2 hz))).add
    ((hasDerivAt_const z (c*(c+2))).div (((hasDerivAt_id z).pow 3).const_mul 4)
      (mul_ne_zero (by norm_num) (pow_ne_zero 3 hz))) using 1
  simp only [signPolynomialCurvature,Pi.pow_apply,id_eq,Nat.reduceSub,pow_one,mul_one,zero_mul,zero_sub]
  field_simp
  ring

/-- Both original signed Hankel polynomials have precisely the same genuine quartic Liouville residual.
Use: polynomialWave_residual bounds the actual forcing propagated into the complex-frequency zero disks.
Article: jacobi, Lemma E.1.
Proof: substitute the actual signed derivatives, clear their genuine nonzero frequency denominator and use s^2=-1 for the outgoing/incoming imaginary signs. -/
theorem signPolynomial_residual {s : ℂ} (hs : s^2= -1) (c : ℂ) {z : ℂ} (hz : z≠0) :
    signPolynomialCurvature s c z+2*s*signPolynomialSlope s c z+c/z^2*signPolynomial s c z=
      -(c*(c+2)*(c+6))/(8*z^4) := by
  unfold signPolynomialCurvature signPolynomialSlope signPolynomial
  field_simp
  ring_nf
  simp only [hs]
  ring

/-- The actual signed complex-frequency Hankel comparison wave.
Use: frequencyHankelApprox combines the two signs with the proved original Bessel connection phase.
Article: jacobi, Lemma E.1.
-/
def polynomialWave (s c z : ℂ) : ℂ := Complex.exp (s*z)*signPolynomial s c z

/-- The actual displayed complex derivative of the original signed Hankel wave.
Use: polynomialWave_hasDerivAt and the normalized true Bessel error supply genuine Cauchy data for complex propagation.
Article: jacobi, Lemma E.1.
-/
def polynomialWaveSlope (s c z : ℂ) : ℂ :=
  Complex.exp (s*z)*(s*signPolynomial s c z+signPolynomialSlope s c z)

/-- The actual displayed complex curvature of the original signed Hankel comparison wave.
Use: polynomialWave_residual is an exact genuine complex-frequency ODE identity.
Article: jacobi, Lemma E.1.
-/
def polynomialWaveCurvature (s c z : ℂ) : ℂ :=
  Complex.exp (s*z)*(s^2*signPolynomial s c z+2*s*signPolynomialSlope s c z+
    signPolynomialCurvature s c z)

/-- The original signed Hankel wave has its genuine displayed complex derivative.
Use: the normalized actual Bessel error has a true derivative along each vertical complex-frequency segment.
Article: jacobi, Lemma E.1.
Proof: apply the actual exponential product rule and the independently proved true rational-amplitude derivative. -/
theorem polynomialWave_hasDerivAt (s c : ℂ) {z : ℂ} (hz : z≠0) :
    HasDerivAt (polynomialWave s c) (polynomialWaveSlope s c z) z := by
  convert! (((hasDerivAt_id z).const_mul s).cexp).mul (signPolynomial_hasDerivAt s c hz) using 1
  simp only [polynomialWaveSlope,id_eq,mul_one]
  ring

/-- The original signed comparison slope has its true displayed complex derivative.
Use: the actual error curvature and its original forced ODE are available throughout every propagation segment.
Article: jacobi, Lemma E.1.
Proof: differentiate the same original exponential and the proved actual signed amplitude derivatives; collect the original three curvature terms. -/
theorem polynomialWaveSlope_hasDerivAt (s c : ℂ) {z : ℂ} (hz : z≠0) :
    HasDerivAt (polynomialWaveSlope s c) (polynomialWaveCurvature s c z) z := by
  convert! (((hasDerivAt_id z).const_mul s).cexp).mul
    (((signPolynomial_hasDerivAt s c hz).const_mul s).add (signPolynomialSlope_hasDerivAt s c hz)) using 1
  simp only [polynomialWaveCurvature,Pi.add_apply,id_eq,mul_one]
  ring

/-- The actual signed comparison wave has the original inverse-fourth-power forced Liouville equation at complex frequency.
Use: frequencyHankelResidual and complex-strip propagation bound the true original Bessel error, with all comparison forcing identities proved.
Article: jacobi, Lemma E.1.
Proof: multiply the genuine signed amplitude residual by its actual exponential factor; s^2=-1 cancels the original free oscillatory term. -/
theorem polynomialWave_residual {s : ℂ} (hs : s^2= -1) (c : ℂ) {z : ℂ} (hz : z≠0) :
    polynomialWaveCurvature s c z+(1+c/z^2)*polynomialWave s c z=
      Complex.exp (s*z)*(-(c*(c+2)*(c+6))/(8*z^4)) := by
  have he := signPolynomial_residual hs c hz
  dsimp only [polynomialWaveCurvature,polynomialWave]
  rw [hs]
  linear_combination Complex.exp (s*z)*he

/-- The original complex-frequency signed polynomials restrict exactly to the already verified real-ray outgoing and incoming amplitudes.
Use: frequencyHankelApprox_ofReal transfers the true original uniform real-ray Bessel remainder to its literal complex-frequency comparison.
Article: jacobi, Lemma E.1.
Proof: evaluate the same actual rational formulas at the included real coordinate, with signs +i and -i. -/
theorem signPolynomial_ofReal (c : ℂ) (x : ℝ) :
    signPolynomial Complex.I c (x:ℂ)=amplitudePolynomial c x ∧
      signPolynomial (-Complex.I) c (x:ℂ)=incomingPolynomial c x := by
  constructor
  · rfl
  · dsimp only [signPolynomial,incomingPolynomial]
    ring

end
end jacobi.Hankel
