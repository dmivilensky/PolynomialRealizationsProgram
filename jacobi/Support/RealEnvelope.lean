import jacobi.Support.Envelope

/-!
Article: jacobi, Appendix C.3 (support weights and segment bounds).
The original complex Envelope lemma gives real polynomial and spectral
derivative bounds on the physical angular interval. The chain rule is
proved for the actual real polynomial, so the derivative factor sin(theta)
is exact and no derivative-comparison premise is needed later.
Use: naturalPolynomial_real_envelope converts the proved angular Envelope estimate to the spectral derivative needed for the genuine interpolated support polynomials.
-/
namespace jacobi.Support
noncomputable section
open Real Filter Polynomial jacobi.Reference
open scoped Topology

/-- The actual complex angular derivative of a real polynomial is its original real spectral derivative times minus sine.
Use: naturalPolynomial_real_envelope converts the proved angular Envelope estimate to the spectral derivative needed for the genuine interpolated support polynomials.
Article: jacobi, Appendix C.3 (support weights and segment bounds).
Source: the polynomial derivative and the ordinary complex chain rule.
Proof: compose the genuine polynomial derivative with the complex cosine derivative, then identify evaluation at a real argument with the real polynomial evaluation. -/
theorem real_polynomial_angular_derivative (p:ℝ[X]) (theta:ℝ) :
    deriv (fun z:ℂ => Polynomial.aeval (Complex.cos z) p) (theta:ℂ)=
      ((-sin theta*p.derivative.eval (cos theta):ℝ):ℂ) := by
  -- Differentiate the actual complex evaluation before restricting its argument and coefficients to the real axis.
  have h := ((p.hasDerivAt_aeval (Complex.cos (theta:ℂ))).comp (theta:ℂ)
    (Complex.hasDerivAt_cos (theta:ℂ))).deriv
  have he : Polynomial.aeval ((cos theta:ℝ):ℂ) p.derivative=
      ((p.derivative.eval (cos theta):ℝ):ℂ) := Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval _ _
  change deriv (fun z:ℂ => Polynomial.aeval (Complex.cos z) p) (theta:ℂ)=_ at h
  rw [← Complex.ofReal_cos,← Complex.ofReal_sin,he] at h
  rw [h]
  push_cast
  ring

/-- The actual real support polynomial and its genuine spectral derivative have the original frequency-decay bounds throughout the physical envelope interval.
Use: supportPolynomial_segment_bounds multiplies these estimates by the same original support weights and applies the proved interpolation sine scale.
Article: jacobi, Appendix C.3 (support weights and segment bounds).
Proof: specialize the complete original complex Envelope lemma to a nonzero real angle. Real evaluation preserves its norm, and the exact chain rule identifies the derivative norm with sin(theta) times the real spectral derivative. Divide by its genuine positive sine. -/
theorem naturalPolynomial_real_envelope {a b:ℝ} (ha:-1<a) (hb:-1<b) :
    ∃C:ℝ,0<C ∧ ∀ᶠn:ℕ in atTop,∀m:ℕ,2*m≤n+3→∀theta:ℝ,
      theta∈Set.Ioo 0 (3*π/4)→
      |(naturalPolynomial a b ha hb n m).eval (cos theta)|≤C*theta^(-gamma a) ∧
      |(naturalPolynomial a b ha hb n m).derivative.eval (cos theta)|≤
        C* jacobi.Jacobi.frequency a b (n+1)*theta^(-gamma a)/sin theta := by
  -- The complex zero-frequency exclusion is discharged by the physical positive angle.
  obtain ⟨C,hC,hbound⟩ := envelope_estimates (bnd:=1) ha hb (by norm_num)
  refine ⟨C,hC,?_⟩
  filter_upwards [hbound] with n hn
  intro m hm theta ht
  have hN := jacobi.Jacobi.frequency_pos ha hb (show 0<n+1 by omega)
  have hsin := sin_pos_of_pos_of_lt_pi ht.1 (by linarith [ht.2,pi_pos])
  have hz : (theta:ℂ)≠0 := Complex.ofReal_ne_zero.mpr ht.1.ne'
  have hre : |(theta:ℂ).re|≤3*π/4 := by simpa only [Complex.ofReal_re,abs_of_pos ht.1] using ht.2.le
  have him : |(theta:ℂ).im|≤1/ jacobi.Jacobi.frequency a b (n+1) := by simp only [Complex.ofReal_im,abs_zero]; positivity
  have hv := (hn m hm).1 (theta:ℂ) hz (hre.trans (by linarith [pi_pos])) him
  have hd := (hn m hm).2 (theta:ℂ) hz hre him
  have hval : naturalWave a b ha hb n m (Complex.cos (theta:ℂ))=
      (((naturalPolynomial a b ha hb n m).eval (cos theta):ℝ):ℂ) := by
    rw [← Complex.ofReal_cos]
    exact Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval _ _
  rw [hval,Complex.norm_real,Real.norm_eq_abs,Complex.norm_real,Real.norm_eq_abs,abs_of_pos ht.1] at hv
  change ‖deriv (fun z:ℂ => Polynomial.aeval (Complex.cos z) (naturalPolynomial a b ha hb n m)) (theta:ℂ)‖≤_ at hd
  rw [real_polynomial_angular_derivative,
    Complex.norm_real,Real.norm_eq_abs,abs_mul,abs_neg,abs_of_pos hsin,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos ht.1] at hd
  constructor
  · exact hv.trans (mul_le_mul_of_nonneg_left (min_le_right _ _) hC.le)
  · apply (le_div_iff₀ hsin).mpr
    have h := hd.trans (mul_le_mul_of_nonneg_left (min_le_right _ _) (mul_pos hC hN).le)
    nlinarith only [h]

end
end jacobi.Support
