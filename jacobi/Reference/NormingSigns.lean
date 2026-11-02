import jacobi.Reference.NormingWeights

/-!
Article: jacobi, Appendix C.2 (exact parity splitting).
The original positive norming weights are the signed reciprocals of
the actual characteristic derivatives, with their exact original
alternating signs. These are the residue coefficients in parity splitting.
Use: norming_signed_reference identifies the precise signed residues used in the original parity contour integral.
-/
namespace jacobi.Reference
noncomputable section
open Real Set _root_.Complex
set_option backward.isDefEq.respectTransparency false

/-- The genuine reference characteristic derivative has exactly its original alternating sign times its genuine norm.
Use: norming_signed_reference identifies the precise signed residues used in the original parity contour integral.
Article: jacobi, Appendix C.2 (exact parity splitting).
Proof: compare the independently proved exact original derivative
and derivative norm formulas. The same positive real Gamma quotient
occurs in both, leaving the original signed power of minus one. -/
theorem characteristicTau_derivative_signed {a : ℝ} (ha : -1<a) (k : ℕ) :
    deriv (characteristicTau a) (eigenvalue a k:ℂ)=
      (-1:ℂ)^(k+1)*(‖deriv (characteristicTau a) (eigenvalue a k:ℂ)‖:ℂ) := by
  rw [characteristicTau_derivative_norm ha,characteristicTau_derivative ha]
  push_cast
  rw [← Complex.Gamma_ofReal]
  push_cast
  ring

/-- The actual inverse reference integral norm is exactly its original signed reciprocal characteristic derivative.
Use: gives the original reference residue coefficient in parity splitting and Proposition C.2.
Article: jacobi, Appendix C.2 (exact parity splitting).
Proof: use the true reference integral norm identity and the proved
actual derivative sign. The original norm and kappa are positive;
the signed power of minus one is nonzero and cancels exactly. -/
theorem norming_signed_reference {a : ℝ} (ha : -1<a) (k : ℕ) :
    (((1/norming a k:ℝ):ℂ))=
      (-1:ℂ)^(k+1)/(((2*Real.pi^2*normConstant a:ℝ):ℂ)*
        deriv (characteristicTau a) (eigenvalue a k:ℂ)) := by
  rw [characteristicTau_derivative_signed ha,norming_characteristicTau ha]
  push_cast
  field_simp

/-- The original defining rho-to-integral-norm weight is exactly the signed reciprocal of the true Bessel characteristic derivative.
Use: supplies the original target residue coefficient in the parity-splitting identity for F and Proposition C.2.
Article: jacobi, Appendix C.2 (exact parity splitting).
Proof: multiply the actual signed reference reciprocal by the actual
positive rho. The proved genuine characteristic derivative identity
substitutes rho*Delta_sigma' for Delta_tau'; the original rho then cancels. -/
theorem norming_signed_bessel {a : ℝ} (ha : -1<a) (k : ℕ) :
    (((normingRatio a ha k/norming a k:ℝ):ℂ))=
      (-1:ℂ)^(k+1)/(((2*Real.pi^2*normConstant a:ℝ):ℂ)*
        deriv (characteristicSigma a) (jacobi.Bessel.sigma a ha k:ℂ)) := by
  have hρ : (normingRatio a ha k:ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr (normingRatio_properties ha k).2.ne'
  have he : ((normingRatio a ha k/norming a k:ℝ):ℂ)=
      (normingRatio a ha k:ℂ)*((1/norming a k:ℝ):ℂ) := by push_cast; ring
  rw [he,norming_signed_reference ha,characteristic_derivative_norming ha]
  field_simp [hρ]

end
end jacobi.Reference
