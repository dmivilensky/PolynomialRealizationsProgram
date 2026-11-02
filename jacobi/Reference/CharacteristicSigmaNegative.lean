import jacobi.Bessel.NegativeLeading
import jacobi.Reference.CharacteristicBessel

/-!
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
The original Bessel characteristic has exactly the article's leading
negative-axis coefficient for every alpha>-1. Its genuine Poisson
integral and three-order recurrence prove the asymptotic for the
previously fixed entire function, including its printed normalization.
Use: removes the true Bessel Gamma normalization in characteristicSigma_negative_asymptotic.
-/
namespace jacobi.Reference
noncomputable section
open Real Set Filter _root_.Complex
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The original Bessel characteristic's fixed central scalar converts the integral-derived Bessel leading coefficient to exactly the printed constant.
Use: removes the true Bessel Gamma normalization in characteristicSigma_negative_asymptotic.
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
Proof: the positive Gamma(alpha+1) cancels and the two genuine powers of two have exponent sum -1. -/
theorem characteristicSigma_negative_constant {a : ℝ} (ha : -1<a) :
    characteristicSigmaConstant a*(Real.Gamma (a+1)*(2:ℝ)^(a-1/2)/Real.sqrt Real.pi)=
      Real.pi^a/(2*Real.sqrt Real.pi) := by
  -- The original central Gamma factor cancels before the genuine powers of two are combined.
  have hG := (Real.Gamma_pos_of_pos (show 0<a+1 by linarith)).ne'
  have ht : (2:ℝ)^(-a-1/2)*(2:ℝ)^(a-1/2)=1/2 := by
    rw [← Real.rpow_add (by norm_num : (0:ℝ)<2),
      show -a-1/2+(a-1/2)=(-1:ℝ) by ring,Real.rpow_neg_one]
    norm_num
  calc
    _ = (Real.pi^a/Real.sqrt Real.pi)*((2:ℝ)^(-a-1/2)*(2:ℝ)^(a-1/2)) := by
      dsimp [characteristicSigmaConstant]
      field_simp [hG]
    _ = _ := by rw [ht]; ring

/-- The literal Bessel characteristic has its exact article negative-axis leading coefficient for every original order alpha>-1.
Use: supplies the Bessel side of the relative characteristic normalization, rather than only its zero set or an unspecified asymptotic factor.
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
Source: Poisson's integral, Watson's lemma and the true Bessel order recurrence, all proved here.
Proof: multiply the actual normalized Bessel leading limit by the
previously fixed printed characteristic scalar and identify the exact
constant. The entire function and its normalization are unchanged. -/
theorem characteristicSigma_negative_asymptotic {a : ℝ} (ha : -1<a) :
    Tendsto (fun y : ℝ => y^(a+1/2)*Real.exp (-y)*
      (characteristicSigma a ((-y^2:ℝ):ℂ)).re)
      atTop (𝓝 (Real.pi^a/(2*Real.sqrt Real.pi))) := by
  have hh := (jacobi.Bessel.normalized_negative_leading ha).const_mul (characteristicSigmaConstant a)
  rw [characteristicSigma_negative_constant ha] at hh
  apply hh.congr'
  filter_upwards with y
  simp only [characteristicSigma,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  ring

/-- The original printed Bessel characteristic is real at every real energy.
Use: upgrades its proved negative-axis limit to the original complex characteristic in the relative normalization comparison.
Article: jacobi, Appendix C.2 (norming ratios).
Proof: the original entire Bessel series has real coefficients at real order and the original fixed characteristic scalar is real. -/
theorem characteristicSigma_real (a E : ℝ) :
    (((characteristicSigma a (E:ℂ)).re:ℝ):ℂ)=characteristicSigma a (E:ℂ) := by
  have h := Complex.conj_eq_iff_re.mp (jacobi.Bessel.normalized_conj a E)
  simp only [characteristicSigma,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  rw [Complex.ofReal_mul,h]

/-- The original complex Bessel characteristic itself has the printed negative-axis asymptotic throughout the complete order range.
Use: compares the same actual complex characteristic with Delta_tau and fixes their relative constant from the two genuine leading limits.
Article: jacobi, Appendix C.2 (norming ratios).
Proof: continuously embed the proved real limit and use the actual characteristic's reality on every real energy. -/
theorem characteristicSigma_negative_complex_asymptotic {a : ℝ} (ha : -1<a) :
    Tendsto (fun y : ℝ => (((y^(a+1/2)*Real.exp (-y):ℝ):ℂ))*
      characteristicSigma a ((-y^2:ℝ):ℂ))
      atTop (𝓝 ((Real.pi^a/(2*Real.sqrt Real.pi):ℝ):ℂ)) := by
  have hh := Complex.continuous_ofReal.continuousAt.tendsto.comp
    (characteristicSigma_negative_asymptotic ha)
  convert! hh using 1
  funext y
  dsimp only [Function.comp_apply]
  simp only [Complex.ofReal_mul,characteristicSigma_real]

end
end jacobi.Reference
