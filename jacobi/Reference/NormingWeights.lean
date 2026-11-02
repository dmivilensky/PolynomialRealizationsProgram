import jacobi.Reference.NormingCharacteristicFormula
import jacobi.Reference.CharacteristicSlope
import jacobi.Reference.CharacteristicWeights

/-!
Article: jacobi, Proposition C.3.
The original integral norming constants and the original gap products
give exactly the article's printed positive Bessel weights. The adjacent
Bessel function in the displayed formula is the actual original J,
whose genuine characteristic derivative was proved independently.
Use: proves normingRatio_div_norming, the original positive spectral weight used by the GL kernel and Proposition C.2.
-/
namespace jacobi.Reference
noncomputable section
open Real Set _root_.Complex
set_option backward.isDefEq.respectTransparency false

/-- The actual squared reference integral norm equals the original kappa times rho times the true Bessel characteristic derivative norm.
Use: proves normingRatio_div_norming, the original positive spectral weight used by the GL kernel and Proposition C.2.
Article: jacobi, Proposition C.3.
Proof: take norms in the proved genuine derivative-ratio identity;
the original rho is strictly positive, and the actual reference norm
already equals kappa times the actual reference derivative norm. -/
theorem norming_bessel_derivative {a : ℝ} (ha : -1<a) (k : ℕ) :
    norming a k=2*Real.pi^2*normConstant a*normingRatio a ha k*
      ‖deriv (characteristicSigma a) (jacobi.Bessel.sigma a ha k:ℂ)‖ := by
  rw [norming_characteristicTau ha,characteristic_derivative_norming ha,norm_mul,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos (normingRatio_properties ha k).2]
  ring

/-- The original defining norming ratio divided by the actual integral norm is exactly the positive reciprocal Bessel derivative weight.
Use: supplies the original weights in the parity residue identity and the midpoint spectral normalization in Proposition C.2.
Article: jacobi, Proposition C.4.
Proof: divide the proved original norming identity by its positive
factors. The actual Bessel spectral zero is genuinely simple, so
the characteristic derivative norm is strictly positive. -/
theorem normingRatio_div_norming {a : ℝ} (ha : -1<a) (k : ℕ) :
    normingRatio a ha k/norming a k=
      1/(2*Real.pi^2*normConstant a*‖deriv (characteristicSigma a) (jacobi.Bessel.sigma a ha k:ℂ)‖) := by
  have hρ := (normingRatio_properties ha k).2.ne'
  rw [norming_bessel_derivative ha]
  field_simp [hρ]

/-- The norm of the genuine original Bessel characteristic derivative has exactly the positive adjacent-order Bessel expression in the article.
Use: identifies the original reciprocal spectral weight with the printed J_(alpha+1) formula.
Article: jacobi, Proposition C.4.
Source: the original Bessel adjacent-order identity, proved in CharacteristicSlope.
Proof: take the norm of the proved actual real derivative formula.
Its real power and original pi and sqrt-two scalars are positive;
only the original adjacent-order Bessel value retains an absolute value. -/
theorem characteristicSigma_derivative_norm {a : ℝ} (ha : -1<a) (k : ℕ) :
    ‖deriv (characteristicSigma a) (jacobi.Bessel.sigma a ha k:ℂ)‖=
      Real.pi^a/(2*Real.sqrt 2)*(jacobi.Bessel.positiveZero a ha k)^(-a-1)*
        |jacobi.Bessel.cylindrical (a+1) (jacobi.Bessel.positiveZero a ha k)| := by
  rw [characteristicSigma_derivative_at_zero ha,Complex.norm_real,Real.norm_eq_abs,
    abs_mul,abs_mul,abs_div,abs_neg,
    abs_of_pos (Real.rpow_pos_of_pos Real.pi_pos a),
    abs_of_pos (show 0<2*Real.sqrt (2:ℝ) by positivity),
    abs_of_pos (Real.rpow_pos_of_pos (jacobi.Bessel.positiveZero_properties ha k).1 _)]

/-- The exact original scalar multiplying the adjacent-Bessel reciprocal weights.
Use: norming_weight_formula identifies this printed constant with the original normingRatio/norming weights of the GL construction.
Article: jacobi, Proposition C.4.
-/
def besselNormingScale (a : ℝ) : ℝ :=
  (2:ℝ)^(a+1)*Real.Gamma (gamma a)^2/(Real.sqrt Real.pi*Real.Gamma (a+3/2)^2)

/-- The printed Bessel norming scalar cancels exactly the original characteristic derivative prefactor and kappa.
Use: proves the fully normalized adjacent-Bessel weight formula from the actual original reciprocal derivative identity.
Article: jacobi, Appendix C.2 (norming ratios).
Proof: substitute the independently proved original norm constant.
The genuine Gamma factors cancel. The pi exponents combine to
sqrt(pi)*pi^(2*gamma); the two powers of two combine to sqrt(2). -/
theorem besselNormingScale_normalization {a : ℝ} (ha : -1<a) :
    (2*Real.pi^2*normConstant a)*(Real.pi^a/(2*Real.sqrt 2))*besselNormingScale a=1 := by
  -- Every original scalar is retained until the exact positive-base power cancellations are applied.
  have hg : 0<gamma a := by linarith [(parameters ha).1]
  have hΓ := (Real.Gamma_pos_of_pos hg).ne'
  have hD := (Real.Gamma_pos_of_pos (show 0<2*gamma a by positivity)).ne'
  have htwo : (2:ℝ)^(1-2*gamma a)*(2:ℝ)^(a+1)=Real.sqrt 2 := by
    rw [← Real.rpow_add (by norm_num : (0:ℝ)<2),
      show 1-2*gamma a+(a+1)=(1/2:ℝ) by dsimp [gamma]; ring,Real.sqrt_eq_rpow]
  have hpi : Real.pi^2*Real.pi^a=Real.sqrt Real.pi*Real.pi^(2*gamma a) := by
    rw [Real.sqrt_eq_rpow,← Real.rpow_two Real.pi,← Real.rpow_add Real.pi_pos,← Real.rpow_add Real.pi_pos]
    congr 1
    dsimp [gamma]
    ring
  have harg : a+3/2=2*gamma a := by dsimp [gamma]; ring
  calc
    _ = ((Real.pi^2*Real.pi^a)/(Real.sqrt Real.pi*Real.pi^(2*gamma a)))*
        (((2:ℝ)^(1-2*gamma a)*(2:ℝ)^(a+1))/Real.sqrt 2) := by
      rw [normConstant,besselNormingScale,harg]
      field_simp [hΓ,hD]
    _ = _ := by rw [hpi,htwo]; field_simp

/-- The adjacent-order Bessel value in the original norming-weight denominator is genuinely nonzero at every original Bessel zero.
Use: the printed J_(alpha+1) reciprocal weight in norming_weight_formula has an actual nonzero denominator.
Article: jacobi, Proposition C.4.
Proof: a zero adjacent-order value would make the proved original characteristic derivative zero, contradicting genuine simplicity of its original spectral zero. -/
theorem adjacent_bessel_ne_zero {a : ℝ} (ha : -1<a) (k : ℕ) :
    jacobi.Bessel.cylindrical (a+1) (jacobi.Bessel.positiveZero a ha k)≠0 := by
  intro hz
  have hd := characteristicSigma_simple ha ((characteristicSigma_zero_iff ha _).mpr ⟨k,rfl⟩)
  apply hd
  rw [characteristicSigma_derivative_at_zero ha,hz,mul_zero,Complex.ofReal_zero]

/-- The original defining rho product divided by the actual reference integral norm has precisely the article's complete printed adjacent-Bessel weight formula.
Use: supplies the fully normalized original positive spectral weights in the kernel, parity splitting and Proposition C.2.
Article: jacobi, Appendix C.2 (norming ratios).
Proof: insert the independently proved original Bessel derivative
norm into the reciprocal-derivative weight. The exact original scalar
normalization cancels kappa and the pi prefactor; the inverse selected
positive power of the actual Bessel zero is j_k^(alpha+1). -/
theorem norming_weight_formula {a : ℝ} (ha : -1<a) (k : ℕ) :
    normingRatio a ha k/norming a k=
      besselNormingScale a*(jacobi.Bessel.positiveZero a ha k)^(a+1)/
        |jacobi.Bessel.cylindrical (a+1) (jacobi.Bessel.positiveZero a ha k)| := by
  -- Every denominator is an original proved nonzero scalar or a genuine simple Bessel spectral derivative.
  rw [normingRatio_div_norming ha,characteristicSigma_derivative_norm ha]
  have hj := (jacobi.Bessel.positiveZero_properties ha k).1
  have hp : (jacobi.Bessel.positiveZero a ha k)^(-a-1)=
      ((jacobi.Bessel.positiveZero a ha k)^(a+1))⁻¹ := by
    rw [show -a-1= -(a+1) by ring,Real.rpow_neg hj.le]
  rw [hp]
  have hc := besselNormingScale_normalization ha
  have hK : (2*Real.pi^2*normConstant a)*(Real.pi^a/(2*Real.sqrt 2))≠0 := by
    exact ne_of_gt (by positivity [normConstant_pos ha])
  have hw : besselNormingScale a=1/((2*Real.pi^2*normConstant a)*(Real.pi^a/(2*Real.sqrt 2))) := by
    apply (eq_div_iff hK).mpr
    linear_combination hc
  rw [hw]
  simp only [mul_inv,inv_inv,div_eq_mul_inv]
  ring

end
end jacobi.Reference
