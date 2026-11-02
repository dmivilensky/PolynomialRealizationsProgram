import jacobi.Reference.CharacteristicNegative

/-!
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
The exact Gamma/beta coefficient of the actual reference characteristic's
negative-axis asymptotic is identified with the printed article constant.
The original beta normalization and the independently computed integral
norm constant are used, so no spectral normalization is stipulated.
Use: removes the beta/Gamma quotient in characteristicTau_negative_leading and gives characteristicTau_negative_asymptotic.
-/
namespace jacobi.Reference
noncomputable section
open Real Set Filter _root_.Complex
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The leading coefficient computed from the original reference beta integral and genuine norm constant is exactly the printed characteristic constant.
Use: removes the beta/Gamma quotient in characteristicTau_negative_leading and gives characteristicTau_negative_asymptotic.
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
Proof: substitute the proved original symmetric beta integral and
the original norm constant. Their Gamma factors cancel exactly.
The positive-base powers of two cancel to two, and the remaining
pi exponent is alpha-1/2 by the original definition of gamma. -/
theorem characteristic_negative_constant {a : ℝ} (ha : -1<a) :
    (Real.Gamma (gamma a)/((2:ℝ)^(gamma a)*betaNormalization (gamma a)))^2/
      (Real.pi^2*normConstant a)=Real.pi^a/(2*Real.sqrt Real.pi) := by
  -- Every canceled factor belongs to the original positive integral normalization.
  have hg : 0<gamma a := by linarith [(parameters ha).1]
  have hG := (Real.Gamma_pos_of_pos hg).ne'
  have hD := (Real.Gamma_pos_of_pos (show 0<2*gamma a by positivity)).ne'
  have h2 := (Real.rpow_pos_of_pos (by norm_num : (0:ℝ)<2) (2*gamma a)).ne'
  have hπ := (Real.rpow_pos_of_pos Real.pi_pos (2*gamma a)).ne'
  have hsq : ((2:ℝ)^(gamma a))^2=(2:ℝ)^(2*gamma a) := by
    rw [← Real.rpow_two ((2:ℝ)^(gamma a)),← Real.rpow_mul (by norm_num : (0:ℝ)≤2)]
    congr 1
    ring
  have htwo : (2:ℝ)^(1-2*gamma a)=2/(2:ℝ)^(2*gamma a) := by
    rw [Real.rpow_sub (by norm_num : (0:ℝ)<2),Real.rpow_one]
  have hpi : Real.pi^a/(2*Real.sqrt Real.pi)=Real.pi^(2*gamma a)/(2*Real.pi^2) := by
    rw [show 2*gamma a=a+(3/2:ℝ) by dsimp [gamma]; ring,
      Real.rpow_add Real.pi_pos]
    have hp : Real.pi^(3/2:ℝ)=Real.pi^2/Real.sqrt Real.pi := by
      rw [Real.sqrt_eq_rpow,← Real.rpow_two Real.pi,← Real.rpow_sub Real.pi_pos]
      congr 1
      ring
    rw [hp]
    field_simp
  rw [hpi,betaNormalization_eq hg,normConstant,htwo,div_pow,mul_pow,hsq]
  field_simp

/-- The literal reference characteristic has exactly the article's leading negative-axis constant, proved from its actual reference integral.
Use: supplies the reference side of the relative-normalization comparison Delta_tau/Delta_sigma in Appendix C.2.
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
Proof: specialize the proved actual reference characteristic limit,
identify its exact integral-derived coefficient and replace
2*gamma-1 by alpha+1/2. No complex-Gamma asymptotic is assumed. -/
theorem characteristicTau_negative_asymptotic {a : ℝ} (ha : -1<a) :
    Tendsto (fun y : ℝ => y^(a+1/2)*Real.exp (-y)*
      (characteristicTau a ((jacobi.Jacobi.endpointCorrection a-y^2:ℝ):ℂ)).re)
      atTop (𝓝 (Real.pi^a/(2*Real.sqrt Real.pi))) := by
  have hh := characteristicTau_negative_leading ha
  rw [characteristic_negative_constant ha,
    show 2*gamma a-1=a+1/2 by dsimp [gamma]; ring] at hh
  exact hh

/-- The literal reference characteristic is real on the whole real energy axis.
Use: the original negative-axis asymptotic applies to the complex characteristic itself in characteristicTau_negative_complex_asymptotic.
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
Proof: the exact midpoint product has two actual real factors at real
energy. Its original nonzero real normalization therefore forces the
imaginary part of the same characteristic to vanish. -/
theorem characteristicTau_real {a : ℝ} (ha : -1<a) (E : ℝ) :
    (((characteristicTau a (E:ℂ)).re:ℝ):ℂ)=characteristicTau a (E:ℂ) := by
  -- The actual midpoint data, rather than an independently chosen real product, fix the characteristic's reality.
  have hp := solution_midpoint_product ha (E:ℂ)
  rw [← solution_real a E (1/2),← solutionSlope_real a E (t := (1/2:ℝ)) (by norm_num)] at hp
  have hi := congrArg Complex.im hp
  simp only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,Complex.re_ofNat,
    Complex.im_ofNat,mul_zero,zero_mul,add_zero] at hi
  have hc : (2*Real.pi^2*normConstant a)≠0 := ne_of_gt (by positivity [normConstant_pos ha])
  have hz := (mul_eq_zero.mp hi.symm).resolve_left hc
  apply Complex.ext
  · rfl
  · simpa only [Complex.ofReal_im] using hz.symm

/-- The original complex reference characteristic itself has the exact printed negative-axis asymptotic, rather than only an estimate for its real part.
Use: supplies the genuine complex-valued reference factor in the relative characteristic comparison used by the original norming and parity formulas.
Article: jacobi, Appendix C.2 (norming ratios).
Proof: apply the continuous real inclusion to the proved exact
real leading limit and use characteristicTau_real for the same
original characteristic at every real negative-axis energy. -/
theorem characteristicTau_negative_complex_asymptotic {a : ℝ} (ha : -1<a) :
    Tendsto (fun y : ℝ => (((y^(a+1/2)*Real.exp (-y):ℝ):ℂ))*
      characteristicTau a ((jacobi.Jacobi.endpointCorrection a-y^2:ℝ):ℂ))
      atTop (𝓝 ((Real.pi^a/(2*Real.sqrt Real.pi):ℝ):ℂ)) := by
  have hh := Complex.continuous_ofReal.continuousAt.tendsto.comp
    (characteristicTau_negative_asymptotic ha)
  convert! hh using 1
  funext y
  dsimp only [Function.comp_apply]
  simp only [Complex.ofReal_mul,characteristicTau_real ha]

end
end jacobi.Reference
