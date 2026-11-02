import jacobi.Reference.CharacteristicBessel
import jacobi.Bessel.OrderShift

/-!
Article: jacobi, Proposition C.4.
The derivative of the literal Delta_sigma is computed using the genuine
next-order Bessel function, with the complete printed scalar. This
identification holds on the whole positive spectral axis, and therefore
at every genuine squared Bessel zero without any additional hypothesis.
Use: supplies the actual nonzero Delta_sigma' values in the source norming weights and characteristic comparison.
-/
namespace jacobi.Reference
noncomputable section
open Real Set _root_.Complex
set_option backward.isDefEq.respectTransparency false

/-- The literal Bessel characteristic derivative has exactly the article's adjacent-order expression on the positive spectral axis.
Use: supplies the actual nonzero Delta_sigma' values in the source norming weights and characteristic comparison.
Article: jacobi, Proposition C.4.
Proof: differentiate the actual normalized entire function and use
the proved adjacent-order series identity. The genuine positive-axis
Bessel normalization, Euler's Gamma recurrence and exact real-power
identities give the original scalar, including the factor sqrt(2). -/
theorem characteristicSigma_derivative {a x : ℝ} (ha : -1<a) (hx : 0<x) :
    deriv (characteristicSigma a) ((x^2:ℝ):ℂ)=
      ((-Real.pi^a/(2*Real.sqrt 2)*x^(-a-1)* jacobi.Bessel.cylindrical (a+1) x:ℝ):ℂ) := by
  -- All special functions here retain their original series and their independently fixed source normalizations.
  have hd := (jacobi.Bessel.normalized_analytic (a:ℂ) ((x^2:ℝ):ℂ)).differentiableAt.hasDerivAt.const_mul
    (characteristicSigmaConstant a:ℂ)
  have he : deriv (characteristicSigma a) ((x^2:ℝ):ℂ)=
      (characteristicSigmaConstant a:ℂ)*deriv (jacobi.Bessel.normalized (a:ℂ)) ((x^2:ℝ):ℂ) := hd.deriv
  rw [he,jacobi.Bessel.normalized_derivative_order_shift (by simpa using ha)]
  have hr : jacobi.Bessel.normalized ((a+1:ℝ):ℂ) ((x^2:ℝ):ℂ)=
      (jacobi.Bessel.realNormalized (a+1) (x^2):ℂ) :=
    (Complex.conj_eq_iff_re.mp (jacobi.Bessel.normalized_conj (a+1) (x^2))).symm
  rw [show (a:ℂ)+1=((a+1:ℝ):ℂ) by push_cast; rfl,hr]
  have hreal : characteristicSigmaConstant a*(-1/(4*(a+1)))*
      jacobi.Bessel.realNormalized (a+1) (x^2)=
        -Real.pi^a/(2*Real.sqrt 2)*x^(-a-1)* jacobi.Bessel.cylindrical (a+1) x := by
    have h2 : (2:ℝ)^(-a-1/2)*(2:ℝ)^(a+1)=Real.sqrt 2 := by
      rw [← Real.rpow_add (by norm_num : (0:ℝ)<2),show -a-1/2+(a+1)=(1/2:ℝ) by ring,
        ← Real.sqrt_eq_rpow]
    have h2' : (2:ℝ)^(-a-1/2)=Real.sqrt 2/(2:ℝ)^(a+1) :=
      (eq_div_iff (Real.rpow_pos_of_pos (by norm_num : (0:ℝ)<2) _).ne').mpr h2
    have ha1 : 0<a+1 := by linarith
    have hG : Real.Gamma (a+1)≠0 := (Real.Gamma_pos_of_pos ha1).ne'
    unfold characteristicSigmaConstant jacobi.Bessel.cylindrical
    rw [Real.Gamma_add_one ha1.ne',h2',
      Real.div_rpow hx.le (by norm_num : (0:ℝ)≤2),show -a-1= -(a+1) by ring,
      Real.rpow_neg hx.le]
    field_simp [hG,ha1.ne',(Real.rpow_pos_of_pos hx (a+1)).ne',
      (Real.rpow_pos_of_pos (by norm_num : (0:ℝ)<2) (a+1)).ne',
      (Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<2)).ne']
    ring_nf
    norm_num
    ring
  push_cast at hreal ⊢
  convert congrArg (fun r : ℝ => (r:ℂ)) hreal using 1 <;> push_cast <;> ring

/-- Every actual squared Bessel zero has the precise printed characteristic derivative in terms of its genuine next-order cylindrical value.
Use: specializes the actual slope formula to the target spectral entries in the source reciprocal-derivative norming rule.
Article: jacobi, Appendix C.2 (norming ratios).
Proof: substitute the positive genuine zero and its proved exact square, with no assumed asymptotic or independently chosen root. -/
theorem characteristicSigma_derivative_at_zero {a : ℝ} (ha : -1<a) (k : ℕ) :
    deriv (characteristicSigma a) (jacobi.Bessel.sigma a ha k:ℂ)=
      ((-Real.pi^a/(2*Real.sqrt 2)*(jacobi.Bessel.positiveZero a ha k)^(-a-1)*
        jacobi.Bessel.cylindrical (a+1) (jacobi.Bessel.positiveZero a ha k):ℝ):ℂ) := by
  simpa only [(jacobi.Bessel.positiveZero_properties ha k).2] using
    characteristicSigma_derivative ha (jacobi.Bessel.positiveZero_properties ha k).1

end
end jacobi.Reference
