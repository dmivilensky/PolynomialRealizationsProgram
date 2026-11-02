import jacobi.Hankel.FrequencyError

/-!
Article: jacobi, Lemma E.1.
Use: frequencyHankelResidual_bound has a uniform true forcing constant independent of the spectral index or the actual frequency real part.
-/
namespace jacobi.Hankel
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- Both actual original Fourier factors have norm at most exp(b) throughout the genuine bounded complex-frequency strip.
Use: frequencyHankelResidual_bound has a uniform true forcing constant independent of the spectral index or the actual frequency real part.
Article: jacobi, Lemma E.1.
Proof: the original two exponent real parts are minus and plus Im(z); bound each by the actual strip width and apply the exponential norm formula. -/
theorem frequency_fourier_bound {z : ℂ} {b : ℝ} (hb : |z.im|≤b) :
    ‖Complex.exp (Complex.I*z)‖≤Real.exp b ∧ ‖Complex.exp (-Complex.I*z)‖≤Real.exp b := by
  -- The two oscillatory factors have opposite real exponential parts.
  constructor
  · rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    simpa only [Complex.mul_re,Complex.I_re,Complex.I_im,zero_mul,one_mul,zero_sub] using
      (neg_le_abs z.im).trans hb
  · rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    simpa only [Complex.mul_re,Complex.neg_re,Complex.neg_im,Complex.I_re,Complex.I_im,
      neg_zero,zero_mul,neg_mul,one_mul,zero_sub,neg_neg] using (le_abs_self z.im).trans hb

/-- The original inverse-square Liouville coefficient is uniformly bounded on the actual far part of a right-half-plane strip.
Use: the real error curvature and complex propagation share the same proved actual coefficient bound 1+B.
Article: jacobi, Lemma E.1.
Proof: |z|>=Re(z)>=1, so the true inverse-square norm is at most one; use the genuine complex triangle and quotient norm identities. -/
theorem frequency_potential_bound {a z : ℂ} {B : ℝ} (ha : ‖besselCoefficient a‖≤B)
    (hz : 1≤z.re) : ‖1+besselCoefficient a/z^2‖≤1+B := by
  have hn : 1≤‖z‖ := hz.trans (Complex.re_le_norm z)
  have hsq : 1≤‖z‖^2 := by nlinarith
  have hd := div_le_self (norm_nonneg (besselCoefficient a)) hsq
  have h := norm_add_le (1:ℂ) (besselCoefficient a/z^2)
  rw [norm_one,norm_div,norm_pow] at h
  linarith

/-- The norm of the original genuine fourth-order Hankel residual coefficient has its exact complex-frequency quotient form.
Use: frequencyHankelResidual_bound controls the actual original forcing by the genuine real part of the complex frequency.
Article: jacobi, Lemma E.1.
Proof: evaluate the actual complex quotient norm and the norm of its original denominator 8*z^4. -/
theorem frequency_residual_norm (a z : ℂ) :
    ‖-(besselCoefficient a*(besselCoefficient a+2)*(besselCoefficient a+6))/(8*z^4)‖=
      ‖besselCoefficient a*(besselCoefficient a+2)*(besselCoefficient a+6)‖/(8*‖z‖^4) := by
  have hd : ‖(8:ℂ)*z^4‖=8*‖z‖^4 := by rw [norm_mul,norm_pow]; norm_num
  rw [norm_div,norm_neg,hd]

/-- The actual original complex Hankel forcing has a quartic bound uniform in the genuine strip and coefficient bounds.
Use: uniform_bessel_frequency_strip discharges P and E from the original common complex-order disk, yielding a true cubic propagated remainder without a numerical or asymptotic certificate.
Article: jacobi, Lemma E.1.
Proof: bound both actual Fourier factors by exp(b), the true phase by E, and the genuine polynomial residual coefficient by P. The original frequency norm is at least its real part, hence at least x. -/
theorem frequencyHankelResidual_bound {a z : ℂ} {x b P E : ℝ} (hx : 0<x) (hxz : x≤z.re)
    (hb : |z.im|≤b) (hP : ‖besselCoefficient a*(besselCoefficient a+2)*(besselCoefficient a+6)‖≤P)
    (hE : ‖besselZeroPhase a‖≤E) :
    ‖frequencyHankelResidual a z‖≤(1+E)*Real.exp b*P/(8*x^4) := by
  -- Every norm bound is for the original explicit fourth-order forcing of the true comparison.
  have hf := frequency_fourier_bound hb
  have hEn : 0≤E := (norm_nonneg _).trans hE
  have hPn : 0≤P := (norm_nonneg _).trans hP
  have hnx : x≤‖z‖ := hxz.trans (Complex.re_le_norm z)
  have hosc : ‖Complex.exp (Complex.I*z)-besselZeroPhase a*Complex.exp (-Complex.I*z)‖≤
      (1+E)*Real.exp b := calc
    _ ≤ ‖Complex.exp (Complex.I*z)‖+‖besselZeroPhase a*Complex.exp (-Complex.I*z)‖ := norm_sub_le _ _
    _ ≤ Real.exp b+E*Real.exp b := by
      rw [norm_mul]
      exact add_le_add hf.1 (mul_le_mul hE hf.2 (norm_nonneg _) hEn)
    _ = _ := by ring
  have hquot : ‖besselCoefficient a*(besselCoefficient a+2)*(besselCoefficient a+6)‖/(8*‖z‖^4)≤P/(8*x^4) := by
    gcongr
  rw [frequencyHankelResidual,norm_mul,frequency_residual_norm]
  exact (mul_le_mul hosc hquot (by positivity) (by positivity)).trans_eq (by ring)

/-- The genuine original normalized complex Bessel error has the actual curvature bound supplied by its proved potential and forcing bounds.
Use: both the initial real Cauchy slope and the complex-segment Gronwall estimate concern this same true original error.
Article: jacobi, Lemma E.1.
Proof: rearrange the actual original error ODE and apply the genuine complex product and triangle inequalities. -/
theorem frequencyError_curvature_bound {R : ℝ} (hR : 0<R) {a z : ℂ} (ha : -1<a.re)
    (hz : z≠0) {K D : ℝ} (hK : ‖1+besselCoefficient a/z^2‖≤K)
    (hD : ‖frequencyHankelResidual a z‖≤D) :
    ‖frequencyErrorCurvature hR a z‖≤K*‖frequencyError hR a z‖+D := by
  have he := frequencyError_equation hR ha hz
  have hv : frequencyErrorCurvature hR a z=
      -(1+besselCoefficient a/z^2)*frequencyError hR a z-frequencyHankelResidual a z := by
    linear_combination he
  rw [hv]
  apply (norm_sub_le _ _).trans
  rw [norm_mul,norm_neg]
  exact add_le_add (mul_le_mul_of_nonneg_right hK (norm_nonneg _)) hD

end
end jacobi.Hankel
