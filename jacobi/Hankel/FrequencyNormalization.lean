import jacobi.Hankel.FrequencySine

/-!
Article: jacobi, Lemma E.1.
Use: frequencyZeroEquation has the exact source sine equation as its leading comparison.
-/
namespace jacobi.Hankel
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- The nonzero original Fourier normalization at a genuine Bessel grid center.
Use: frequencyZeroEquation has the exact source sine equation as its leading comparison.
Article: jacobi, Lemma E.1.
-/
def frequencyNormalizer (a : ℂ) (k : ℕ) : ℂ :=
  2*Complex.I*Complex.exp (Complex.I*frequencyGrid a k)

/-- The genuine grid Fourier normalization never vanishes.
Use: dividing by frequencyNormalizer preserves all original Bessel zeros and their simplicity.
Article: jacobi, Lemma E.1.
Proof: two, i, and every actual complex exponential are nonzero. -/
theorem frequencyNormalizer_ne_zero (a : ℂ) (k : ℕ) : frequencyNormalizer a k≠0 :=
  mul_ne_zero (mul_ne_zero (by norm_num) Complex.I_ne_zero) (Complex.exp_ne_zero _)

/-- The actual original Bessel zero equation in one genuine phase-grid frequency disk.
Use: the quantitative zero-disk theorem is applied to this function after the actual cubic value and slope errors are bounded.
Article: jacobi, Lemma E.1.
-/
def frequencyZeroEquation {R : ℝ} (hR : 0<R) (a : ℂ) (k : ℕ) (ζ : ℂ) : ℂ :=
  (frequencyWave a (frequencyGrid a k+ζ)/outgoingBesselCoefficient hR a)/frequencyNormalizer a k

/-- The genuine displayed derivative of the actual original Bessel frequency-disk zero equation.
Use: the zero-disk derivative contraction and nonzero slope concern the original Bessel function itself.
Article: jacobi, Lemma E.1.
-/
def frequencyZeroSlope {R : ℝ} (hR : 0<R) (a : ℂ) (k : ℕ) (ζ : ℂ) : ℂ :=
  (frequencySlope a (frequencyGrid a k+ζ)/outgoingBesselCoefficient hR a)/frequencyNormalizer a k

/-- The actual original zero equation has the displayed genuine complex derivative in its original right-half-plane disk.
Use: the quantitative unique-zero theorem has a proved derivative for the exact original Bessel equation.
Article: jacobi, Lemma E.1.
Proof: compose the original complex Bessel derivative with the actual grid translation and divide by the two fixed original normalizing factors. -/
theorem frequencyZeroEquation_hasDerivAt {R : ℝ} (hR : 0<R) (a : ℂ) (k : ℕ) {ζ : ℂ}
    (hz : frequencyGrid a k+ζ∈Complex.slitPlane) :
    HasDerivAt (frequencyZeroEquation hR a k) (frequencyZeroSlope hR a k ζ) ζ := by
  convert! (((frequencyWave_hasDerivAt a hz).comp ζ
    ((hasDerivAt_id ζ).const_add (frequencyGrid a k))).div_const
      (outgoingBesselCoefficient hR a)).div_const (frequencyNormalizer a k) using 1
  simp only [frequencyZeroSlope,mul_one]

/-- The genuine Bessel disk equation and its derivative have exactly their displayed sine comparisons plus the original normalized cubic errors.
Use: frequencyZeroEquation bounds and its actual contraction use no assumed asymptotic equation or differentiated remainder.
Article: jacobi, Lemma E.1.
Proof: rearrange the definitions of the actual Bessel errors and substitute the independently proved exact Hankel sine value and derivative identities; both true Fourier normalizations are nonzero. -/
theorem frequencyZeroEquation_expansion {R : ℝ} (hR : 0<R) (a : ℂ) (k : ℕ) {ζ : ℂ}
    (hz : frequencyGrid a k+ζ≠0) :
    frequencyZeroEquation hR a k ζ=frequencySine (besselCoefficient a) (frequencyGrid a k) ζ+
      frequencyError hR a (frequencyGrid a k+ζ)/frequencyNormalizer a k ∧
    frequencyZeroSlope hR a k ζ=frequencySineSlope (besselCoefficient a) (frequencyGrid a k) ζ+
      frequencyErrorSlope hR a (frequencyGrid a k+ζ)/frequencyNormalizer a k := by
  -- Both exact comparisons retain the actual nonzero Fourier normalization.
  have hv := frequencyHankel_sine a k ζ
  have hd := frequencyHankel_sineSlope a k hz
  change frequencyHankelApprox a (frequencyGrid a k+ζ)=frequencyNormalizer a k*frequencySine _ _ _ at hv
  change frequencyHankelSlope a (frequencyGrid a k+ζ)=frequencyNormalizer a k*frequencySineSlope _ _ _ at hd
  constructor
  · unfold frequencyZeroEquation frequencyError
    rw [hv]
    field_simp [frequencyNormalizer_ne_zero a k]
    ring
  · unfold frequencyZeroSlope frequencyErrorSlope
    rw [hd]
    field_simp [frequencyNormalizer_ne_zero a k]
    ring

/-- Division by the genuine original grid normalization has an exact real norm formula.
Use: the original cubic Bessel value and derivative errors stay cubic uniformly on every genuine bounded order disk.
Article: jacobi, Lemma E.1.
Proof: the true Fourier exponential has real exponent -Im(varpi_k); its reciprocal norm is exp(Im(varpi_k)), with the exact factor one half. -/
theorem frequencyNormalizer_quotient_norm (a w : ℂ) (k : ℕ) :
    ‖w/frequencyNormalizer a k‖=‖w‖*Real.exp ((frequencyGrid a k).im)/2 := by
  -- The original normalizing factor is explicit and has no unknown leading-amplitude estimate.
  have he : (Complex.I*frequencyGrid a k).re= -(frequencyGrid a k).im := by simp [Complex.mul_re]
  rw [norm_div,frequencyNormalizer,norm_mul,norm_mul,Complex.norm_I,Complex.norm_exp,he]
  norm_num only [Complex.norm_ofNat,mul_one]
  rw [Real.exp_neg]
  field_simp

end
end jacobi.Hankel
