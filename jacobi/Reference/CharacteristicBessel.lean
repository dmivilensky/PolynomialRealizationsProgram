import jacobi.Reference.Parameters
import jacobi.Bessel.EdgeData

/-!
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
The Bessel characteristic keeps the article's literal normalization,
not merely its zero set. Its actual entire function, convergent series,
canonical product and complete simple zero set are identified directly
with the Bessel theory already proved in this project.
Use: fixes the scalar in characteristicSigma and its norming derivative; a zero-set identification alone would leave it undetermined.
-/
namespace jacobi.Reference
noncomputable section
open Real Set _root_.Complex
set_option backward.isDefEq.respectTransparency false

/-- The precise nonzero central normalization of the article's Bessel characteristic.
Use: fixes the scalar in characteristicSigma and its norming derivative; a zero-set identification alone would leave it undetermined.
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
-/
def characteristicSigmaConstant (a : ℝ) : ℝ :=
  Real.pi^a*(2:ℝ)^(-a-1/2)/Real.Gamma (a+1)

/-- The actual Bessel characteristic in the spectral variable, with the printed normalization.
Use: supplies Delta_sigma in the source norming formulas, midpoint identity and Proposition C.2.
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
-/
def characteristicSigma (a : ℝ) (z : ℂ) : ℂ :=
  (characteristicSigmaConstant a:ℂ)* jacobi.Bessel.normalized (a:ℂ) z

/-- The literal central Bessel characteristic normalization is strictly positive throughout alpha>-1.
Use: characteristicSigma preserves exactly the actual Bessel zeros and their simplicity.
Article: jacobi, Appendix C.2 (exact parity splitting).
Proof: pi, two and Gamma(alpha+1) are positive in the original parameter range. -/
theorem characteristicSigmaConstant_pos {a : ℝ} (ha : -1<a) :
    0<characteristicSigmaConstant a := by
  unfold characteristicSigmaConstant
  exact div_pos (mul_pos (Real.rpow_pos_of_pos Real.pi_pos _)
    (Real.rpow_pos_of_pos (by norm_num) _)) (Real.Gamma_pos_of_pos (by linarith))

/-- The source Bessel characteristic is genuinely entire in its actual energy variable.
Use: justifies its actual complex derivatives and the characteristic contour argument.
Article: jacobi, Appendix C.2 (norming ratios).
Proof: multiply the previously proved actual entire normalized Bessel function by the literal fixed scalar. -/
theorem characteristicSigma_analytic (a : ℝ) (z : ℂ) :
    AnalyticAt ℂ (characteristicSigma a) z :=
  analyticAt_const.mul (jacobi.Bessel.normalized_analytic (a:ℂ) z)

/-- The Bessel characteristic has the exact printed central value.
Use: fixes the constant in its genuine canonical product and distinguishes this normalization from an arbitrary function with the same zeros.
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
Proof: the actual normalized Bessel function equals one at zero. -/
theorem characteristicSigma_zero {a : ℝ} (ha : -1<a) :
    characteristicSigma a 0=(characteristicSigmaConstant a:ℂ) := by
  rw [characteristicSigma,jacobi.Bessel.normalized_zero (by simpa using ha),mul_one]

/-- The literal Bessel characteristic vanishes exactly at the original squared Bessel zeros, with no other complex zeros.
Use: supplies the complete target characteristic zero set to the parity and midpoint arguments.
Article: jacobi, Appendix C.2 (exact parity splitting).
Proof: its scalar is nonzero. The actual Bessel zero-location theorem
makes every complex zero positive real, and its proved exhaustive
enumeration lists every such zero exactly once. -/
theorem characteristicSigma_zero_iff {a : ℝ} (ha : -1<a) (z : ℂ) :
    characteristicSigma a z=0 ↔ ∃ k : ℕ,z=(jacobi.Bessel.sigma a ha k:ℂ) := by
  -- Zero location and exhaustive enumeration are reused for the same normalized source function.
  have hc : (characteristicSigmaConstant a:ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr (characteristicSigmaConstant_pos ha).ne'
  rw [characteristicSigma,mul_eq_zero,or_iff_right hc]
  constructor
  · intro hz
    obtain ⟨x,_,hx⟩ := jacobi.Bessel.normalized_zero_positive ha hz
    have hx0 : x∈jacobi.Bessel.spectralZeros a := by
      change jacobi.Bessel.normalized (a:ℂ) (x:ℂ)=0
      rwa [← hx]
    obtain ⟨k,hk⟩ := jacobi.Bessel.sigma_exhaustive ha hx0
    exact ⟨k,by rw [hx,hk]⟩
  · rintro ⟨k,rfl⟩
    exact jacobi.Bessel.sigma_mem ha k

/-- Every zero of the literal Bessel characteristic is simple.
Use: all actual reciprocal-derivative target norming factors have a nonzero denominator.
Article: jacobi, Appendix C.2 (norming ratios).
Proof: the true derivative is the nonzero printed scalar times the
derivative of the actual Bessel function; its zeros are already proved simple. -/
theorem characteristicSigma_simple {a : ℝ} (ha : -1<a) {z : ℂ}
    (hz : characteristicSigma a z=0) : deriv (characteristicSigma a) z≠0 := by
  have hc : (characteristicSigmaConstant a:ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr (characteristicSigmaConstant_pos ha).ne'
  have hf : jacobi.Bessel.normalized (a:ℂ) z=0 := (mul_eq_zero.mp hz).resolve_left hc
  have hd := (jacobi.Bessel.normalized_analytic (a:ℂ) z).differentiableAt.hasDerivAt.const_mul
    (characteristicSigmaConstant a:ℂ)
  rw [show deriv (characteristicSigma a) z=
    (characteristicSigmaConstant a:ℂ)*deriv (jacobi.Bessel.normalized (a:ℂ)) z from hd.deriv]
  exact mul_ne_zero hc (jacobi.Bessel.normalized_zero_simple (by simpa using ha) hf)

/-- The actual Bessel characteristic has its genuine convergent product with exactly the article's prefactor.
Use: starts the source characteristic comparison without an arbitrary missing normalization constant.
Article: jacobi, Appendix C.2 (norming ratios).
Proof: the true normalized Bessel canonical product was proved from
finite Jacobi products and their full spectral limit. Multiply it by
the independently specified printed central value. -/
theorem characteristicSigma_product {a : ℝ} (ha : -1<a) (z : ℂ) :
    characteristicSigma a z=characteristicSigma a 0*
      ∏' k : ℕ,(1-z/(jacobi.Bessel.sigma a ha k:ℂ)) := by
  rw [characteristicSigma_zero ha,characteristicSigma,jacobi.Bessel.canonical_product ha z]

end
end jacobi.Reference
