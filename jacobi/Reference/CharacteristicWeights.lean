import jacobi.Reference.CharacteristicNorming

/-!
Article: jacobi, Appendix C.2 (exact parity splitting).
The computed literal characteristic derivatives are nonzero and their
absolute values equal the actual squared reference norms after the exact
factor 2*pi^2*A(gamma). These are integral norms, not stipulated weights.
Use: identifies genuine integral norming constants with characteristic derivatives and proves simplicity.
-/
namespace jacobi.Reference
noncomputable section
open Real Set _root_.Complex
set_option backward.isDefEq.respectTransparency false

/-- The absolute characteristic derivative has the exact positive Gamma quotient at every reference eigenvalue.
Use: identifies genuine integral norming constants with characteristic derivatives and proves simplicity.
Article: jacobi, Appendix C.2 (exact parity splitting).
Proof: the exact derivative has alternating unit sign. Every real
denominator factor is strictly positive in the source parameter range,
so the complex norm is precisely the unsigned real quotient. -/
theorem characteristicTau_derivative_norm {a : ℝ} (ha : -1<a) (k : ℕ) :
    ‖deriv (characteristicTau a) (eigenvalue a k:ℂ)‖=
      (k.factorial:ℝ)/(2*Real.pi^2*((k:ℝ)+gamma a)*Real.Gamma ((k:ℝ)+2*gamma a)) := by
  -- The real Gamma embedding is identified before taking norms of the actual complex derivative.
  have hg : 0<gamma a := by linarith [(parameters ha).1]
  have hx : 0<(k:ℝ)+gamma a := by positivity
  have hGamma := Real.Gamma_pos_of_pos (show 0<(k:ℝ)+2*gamma a by positivity)
  have hG : Complex.Gamma ((k:ℂ)+2*(gamma a:ℂ))=
      (Real.Gamma ((k:ℝ)+2*gamma a):ℂ) := by
    rw [← Complex.Gamma_ofReal]
    congr 1
    push_cast
    rfl
  rw [characteristicTau_derivative ha,hG,norm_div,norm_mul,norm_pow]
  have hden : 2*(Real.pi:ℂ)^2*((k:ℂ)+(gamma a:ℂ))*
      (Real.Gamma ((k:ℝ)+2*gamma a):ℂ)=
      ((2*Real.pi^2*((k:ℝ)+gamma a)*Real.Gamma ((k:ℝ)+2*gamma a):ℝ):ℂ) := by push_cast; rfl
  rw [hden,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (by positivity :
    0<2*Real.pi^2*((k:ℝ)+gamma a)*Real.Gamma ((k:ℝ)+2*gamma a))]
  simp

/-- Every zero of the literal reference characteristic is simple throughout alpha>-1.
Use: all actual source reciprocal-derivative formulas use genuinely nonzero denominators.
Article: jacobi, Proposition C.3.
Proof: its exact derivative norm is a quotient of strictly positive factors, including the nonzero factorial. -/
theorem characteristicTau_simple {a : ℝ} (ha : -1<a) {z : ℂ}
    (hz : characteristicTau a z=0) : deriv (characteristicTau a) z≠0 := by
  obtain ⟨k,rfl⟩ := (characteristicTau_zero_iff a z).mp hz
  apply norm_pos_iff.mp
  rw [characteristicTau_derivative_norm ha]
  have hg : 0<gamma a := by linarith [(parameters ha).1]
  exact div_pos (Nat.cast_pos.mpr (Nat.factorial_pos k)) (by
    apply mul_pos (by positivity)
    exact Real.Gamma_pos_of_pos (by positivity))

/-- The independently defined true reference squared integral norm is exactly 2*pi^2*A(gamma) times the absolute derivative of the literal characteristic.
Use: discharges the reference normalization in the original signed residue and norming-ratio formulas used for Proposition C.2.
Article: jacobi, Appendix C.2 (norming ratios).
Proof: substitute the genuine integral norm evaluation and the actual
characteristic derivative norm. Euler's Gamma value at a positive integer
is the same factorial; cancel the positive real factors. -/
theorem norming_characteristicTau {a : ℝ} (ha : -1<a) (k : ℕ) :
    norming a k=2*Real.pi^2*normConstant a*
      ‖deriv (characteristicTau a) (eigenvalue a k:ℂ)‖ := by
  -- Both sides refer to previously fixed actual objects, so this is an identification, not a normalization convention.
  rw [norming_formula ha,characteristicTau_derivative_norm ha,Real.Gamma_nat_eq_factorial]
  have hg : 0<gamma a := by linarith [(parameters ha).1]
  field_simp [Real.pi_ne_zero,ne_of_gt (show 0<(k:ℝ)+gamma a by positivity),
    (Real.Gamma_pos_of_pos (show 0<(k:ℝ)+2*gamma a by positivity)).ne']

end
end jacobi.Reference
