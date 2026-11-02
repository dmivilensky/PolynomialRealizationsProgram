import jacobi.Hankel.FrequencyGrid

/-!
Article: jacobi, Lemma E.1.
Its differentiated formula is exact as well. These identities keep
the nonzero Fourier normalization explicit in the zero construction.
Use: the actual Bessel zero equation differs from this displayed function only by its proved cubic error.
-/
namespace jacobi.Hankel
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- The exact original Hankel sine equation after moving the frequency origin to a genuine phase-grid center.
Use: the actual Bessel zero equation differs from this displayed function only by its proved cubic error.
Article: jacobi, Lemma E.1.
-/
def frequencySine (c q ζ : ℂ) : ℂ :=
  (1-c*(c+2)/(8*(q+ζ)^2))*Complex.sin ζ-c/(2*(q+ζ))*Complex.cos ζ

/-- The actual derivative of the displayed original Hankel sine equation in a moving complex frequency disk.
Use: the zero-disk contraction bound compares this exact derivative with one and then adds the genuine original Bessel error derivative.
Article: jacobi, Lemma E.1.
-/
def frequencySineSlope (c q ζ : ℂ) : ℂ :=
  (1-c*(c+2)/(8*(q+ζ)^2))*Complex.cos ζ+
    c*(c+2)/(4*(q+ζ)^3)*Complex.sin ζ+
    c/(2*(q+ζ)^2)*Complex.cos ζ+c/(2*(q+ζ))*Complex.sin ζ

/-- The true original Hankel sine equation has its displayed complex derivative at every nonzero actual frequency.
Use: frequencyHankel_sineSlope identifies the independently differentiated genuine Hankel comparison with the same actual derivative.
Article: jacobi, Lemma E.1.
Proof: differentiate the genuine rational coefficients, sine and cosine; collect the four original terms by field algebra. -/
theorem frequencySine_hasDerivAt (c q : ℂ) {ζ : ℂ} (hz : q+ζ≠0) :
    HasDerivAt (frequencySine c q) (frequencySineSlope c q ζ) ζ := by
  -- The only possible rational singularity is the original frequency zero, excluded here.
  have hd := (hasDerivAt_id ζ).const_add q
  have h1 := (hd.pow 2).const_mul (8:ℂ)
  have h2 := hd.const_mul (2:ℂ)
  have hh := (((hasDerivAt_const ζ (1:ℂ)).sub
    ((hasDerivAt_const ζ (c*(c+2))).div h1 (mul_ne_zero (by norm_num) (pow_ne_zero 2 hz)))).mul
      (Complex.hasDerivAt_sin ζ)).sub
    (((hasDerivAt_const ζ c).div h2 (mul_ne_zero (by norm_num) hz)).mul (Complex.hasDerivAt_cos ζ))
  convert! hh using 1
  dsimp [frequencySineSlope]
  field_simp
  ring

/-- The actual original canonical Hankel comparison equals its exact sine equation in every genuine phase-grid disk.
Use: the Bessel frequency-disk residual is now an error around sin(zeta) with actual rational first and second corrections, rather than an assumed asymptotic equation.
Article: jacobi, Lemma E.1.
Proof: the genuine doubled grid phase is the original Bessel connection phase. Factor exp(i*varpi_k) from the actual two waves; the remaining exact exponentials are the community sine and cosine formulas. -/
theorem frequencyHankel_sine (a : ℂ) (k : ℕ) (ζ : ℂ) :
    frequencyHankelApprox a (frequencyGrid a k+ζ)=
      (2*Complex.I*Complex.exp (Complex.I*frequencyGrid a k))*
        frequencySine (besselCoefficient a) (frequencyGrid a k) ζ := by
  -- The genuine phase identity removes the full integer index without discarding its source normalization.
  let q := frequencyGrid a k
  have he : besselZeroPhase a*Complex.exp (-Complex.I*(q+ζ))=
      Complex.exp (Complex.I*q)*Complex.exp (-Complex.I*ζ) := by
    rw [← frequencyGrid_phase a k,← Complex.exp_add,← Complex.exp_add]
    congr 1
    dsimp only [q]
    ring
  unfold frequencyHankelApprox polynomialWave
  rw [show Complex.I*(frequencyGrid a k+ζ)=Complex.I*frequencyGrid a k+Complex.I*ζ by ring,
    Complex.exp_add]
  rw [show besselZeroPhase a*(Complex.exp (-Complex.I*(frequencyGrid a k+ζ))*
      signPolynomial (-Complex.I) (besselCoefficient a) (frequencyGrid a k+ζ))=
      (besselZeroPhase a*Complex.exp (-Complex.I*(frequencyGrid a k+ζ)))*
        signPolynomial (-Complex.I) (besselCoefficient a) (frequencyGrid a k+ζ) by ring,he]
  simp only [frequencySine,signPolynomial,Complex.sin,Complex.cos]
  simp only [show ζ*Complex.I=Complex.I*ζ by ring,show -ζ*Complex.I= -Complex.I*ζ by ring]
  field_simp
  ring_nf
  simp only [Complex.I_sq]
  ring

/-- The actual differentiated Hankel comparison has the exact same sine-equation normalization.
Use: the true zero-disk derivative bound combines this actual derivative with the independently proved original cubic error derivative.
Article: jacobi, Lemma E.1.
Proof: differentiate the proved original Hankel sine identity along the actual translated frequency and use uniqueness of the complex derivative. -/
theorem frequencyHankel_sineSlope (a : ℂ) (k : ℕ) {ζ : ℂ} (hz : frequencyGrid a k+ζ≠0) :
    frequencyHankelSlope a (frequencyGrid a k+ζ)=
      (2*Complex.I*Complex.exp (Complex.I*frequencyGrid a k))*
        frequencySineSlope (besselCoefficient a) (frequencyGrid a k) ζ := by
  -- Both sides are derivatives of the same exact original translated Hankel comparison.
  have hd := (frequencyHankelApprox_hasDerivAt a hz).comp ζ
    ((hasDerivAt_id ζ).const_add (frequencyGrid a k))
  have hs := (frequencySine_hasDerivAt (besselCoefficient a) (frequencyGrid a k) hz).const_mul
    (2*Complex.I*Complex.exp (Complex.I*frequencyGrid a k))
  have he : (fun z : ℂ => frequencyHankelApprox a (frequencyGrid a k+z))=
      (fun z : ℂ => (2*Complex.I*Complex.exp (Complex.I*frequencyGrid a k))*
        frequencySine (besselCoefficient a) (frequencyGrid a k) z) :=
    funext (frequencyHankel_sine a k)
  change HasDerivAt (fun z : ℂ => frequencyHankelApprox a (frequencyGrid a k+z))
    (frequencyHankelSlope a (frequencyGrid a k+ζ)*1) ζ at hd
  rw [he] at hd
  simpa only [mul_one] using hd.unique hs

end
end jacobi.Hankel
