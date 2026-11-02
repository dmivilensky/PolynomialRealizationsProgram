import jacobi.Reference.Orthogonality
import jacobi.Reference.JacobiNorm

/-!
Article: jacobi, Lemma C.1.
The source norming constants are evaluated from their genuine integrals.
The displayed scalar A(gamma) is identified exactly by the community
Gamma duplication formula, rather than assumed as a normalization rule.
Use: fixes the common scalar in both reference and Bessel reciprocal-derivative norming rules.
-/
namespace jacobi.Reference
noncomputable section
open Real
set_option backward.isDefEq.respectTransparency false

/-- The literal normalization constant A(gamma) in the article's reference norm formula.
Use: fixes the common scalar in both reference and Bessel reciprocal-derivative norming rules.
Article: jacobi, Lemma C.1.
-/
def normConstant (a : ℝ) : ℝ :=
  (2:ℝ)^(1-2*gamma a)*Real.Gamma (2*gamma a)^2/
    (Real.pi^(2*gamma a)*Real.Gamma (gamma a)^2)

/-- The literal source normalization constant is exactly the positive scalar produced by the actual Jacobi norm and cosine substitution.
Use: identifies the original article's printed Gamma normalization with the independently proved genuine norm integral.
Article: jacobi, Lemma C.1.
Source: Legendre's Gamma duplication formula, Real.Gamma_mul_Gamma_add_half.
Proof: square the genuine duplication formula. The exact scalar
2^(1-2*gamma)=2/2^(2*gamma) and the true coordinate scale cancel all
remaining powers of two and pi; the positive Gamma denominators are nonzero. -/
theorem normConstant_eq {a : ℝ} (ha : -1<a) :
    normConstant a=Real.Gamma (gamma a+1/2)^2/(2*coordinateScale a) := by
  -- All scalars are the literal source quantities, with the original positive reference exponent.
  have hg : 0<gamma a := by linarith [(parameters ha).1]
  have hpow : (2:ℝ)^(1-2*gamma a)=2/(2:ℝ)^(2*gamma a) := by
    rw [Real.rpow_sub (by norm_num : (0:ℝ)<2),Real.rpow_one]
  have hd := congrArg (fun x : ℝ => x^2) (Real.Gamma_mul_Gamma_add_half (gamma a))
  rw [mul_pow,mul_pow,mul_pow,Real.sq_sqrt Real.pi_pos.le,hpow] at hd
  unfold normConstant coordinateScale
  rw [hpow,Real.div_rpow Real.pi_pos.le (by norm_num)]
  field_simp [(Real.Gamma_pos_of_pos hg).ne',
    (Real.rpow_pos_of_pos Real.pi_pos (2*gamma a)).ne',
    (Real.rpow_pos_of_pos (by norm_num : (0:ℝ)<2) (2*gamma a)).ne'] at hd ⊢
  nlinarith [hd]

/-- The original reference normalization scalar is strictly positive throughout the full source order range.
Use: the source reciprocal-derivative weights and norming constants have the required positive normalization.
Article: jacobi, Lemma C.1.
Proof: its equivalent Gamma-square value has positive numerator and the true coordinate denominator is positive. -/
theorem normConstant_pos {a : ℝ} (ha : -1<a) : 0<normConstant a := by
  rw [normConstant_eq ha]
  apply div_pos _ (mul_pos (by norm_num) (coordinateScale_pos a))
  exact sq_pos_of_pos (Real.Gamma_pos_of_pos (by linarith [(parameters ha).1]))

/-- Every genuine original reference squared norm has exactly the article's printed Gamma value.
Use: supplies the actual norming constants in the GL kernel and the reference spectral basis, without a norm-formula premise.
Article: jacobi, Lemma C.1.
Proof: use the exact actual cosine-coordinate norm formula and the
genuine weighted Jacobi Gamma norm. The equal-parameter Gamma factors
cancel, and the duplication identity gives precisely the printed A. -/
theorem norming_formula {a : ℝ} (ha : -1<a) (k : ℕ) :
    norming a k=normConstant a*Real.Gamma ((k:ℝ)+1)/
      (((k:ℝ)+gamma a)*Real.Gamma ((k:ℝ)+2*gamma a)) := by
  -- Norming is the original convergent integral, not a Gamma expression stipulated as a definition.
  have hg : 0<gamma a := by linarith [(parameters ha).1]
  rw [norming_eq,normConstant_eq ha,
    jacobiNorm_formula (parameters ha).2 (parameters ha).2 (by dsimp [jacobiIndex]; linarith)]
  have hindex : jacobiIndex a+1=gamma a+1/2 := by dsimp [jacobiIndex]; ring
  have hsame : (k:ℝ)+jacobiIndex a+1=(k:ℝ)+gamma a+1/2 := by dsimp [jacobiIndex]; ring
  have hsum : (k:ℝ)+jacobiIndex a+jacobiIndex a+1=(k:ℝ)+2*gamma a := by dsimp [jacobiIndex]; ring
  have hfactor : 2*(k:ℝ)+jacobiIndex a+jacobiIndex a+1=2*((k:ℝ)+gamma a) := by dsimp [jacobiIndex]; ring
  rw [hindex,hsame,hsum,hfactor,← Real.Gamma_nat_eq_factorial]
  have hk : 0<(k:ℝ)+gamma a := by positivity
  field_simp [(coordinateScale_pos a).ne',hk.ne',
    (Real.Gamma_pos_of_pos (show 0<(k:ℝ)+gamma a+1/2 by positivity)).ne',
    (Real.Gamma_pos_of_pos (show 0<(k:ℝ)+2*gamma a by positivity)).ne']

end
end jacobi.Reference
