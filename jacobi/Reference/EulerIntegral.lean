import jacobi.Reference.BetaConvolution
import jacobi.Reference.EulerTransformation

/-!
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
Euler's integral for the actual community Gauss function is deduced from
the already proved beta convolution. Its denominator parameters are real
and positive; the numerator exponent can be arbitrary and complex.
Source: Euler's hypergeometric integral, DLMF 15.6.1.
Use: Euler's transformation gives the binomial function in binomial.
-/
namespace jacobi.Reference.Hypergeometric
noncomputable section
open Set MeasureTheory _root_.Complex Polynomial
set_option backward.isDefEq.respectTransparency false

/-- A zero numerator makes the actual Gauss function identically one.
Use: Euler's transformation gives the binomial function in binomial.
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
Source: the terminating hypergeometric series, DLMF 15.2.1.
Proof: every positive-degree rising factorial at zero vanishes. -/
theorem zero_numerator (a c z : ℂ) : ordinaryHypergeometric a 0 c z=1 := by
  rw [ordinaryHypergeometric_eq_tsum]
  dsimp only
  rw [tsum_eq_single 0]
  · simp
  · intro n hn
    simp [ascPochhammer_ne_zero_eval_zero ℂ hn]

/-- Cancelling an equal positive-real-part numerator and denominator gives the actual binomial function on its original convergence disk.
Use: substitutes the genuine power into beta_convolution to prove euler_integral.
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
Source: the binomial theorem, DLMF 15.4.6, proved here using Euler's transformation.
Proof: the Euler-transformed second numerator is zero and its exponent is -a. -/
theorem binomial {a b z : ℂ} (hb : 0<b.re) (hz : ‖z‖<1) :
    ordinaryHypergeometric a b b z=(1-z)^(-a) := by
  rw [euler_transform hb hz,sub_self,zero_numerator,mul_one]
  congr 1
  ring

/-- Euler's integral holds for the actual Gauss function with its exact original beta normalization.
Use: evaluates the original midpoint hypergeometric value by two monotone changes of variables in SecondSummationIntegral.
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
Source: Euler's hypergeometric integral, DLMF 15.6.1; deduced from the already proved dominated beta convolution.
Proof: the integrand of beta_convolution is the genuine binomial function at z*u, which remains in the open unit disk on the whole integration interval. -/
theorem euler_integral (a : ℂ) {b d : ℝ} (hb : 0<b) (hd : 0<d)
    {z : ℂ} (hz : ‖z‖<1) :
    (∫ u in (0:ℝ)..1,(jacobi.Jacobi.weight (b-1) (d-1) u:ℂ)*(1-z*(u:ℂ))^(-a))=
      (Complex.Gamma (b:ℂ)*Complex.Gamma (d:ℂ)/Complex.Gamma ((b:ℂ)+(d:ℂ)))*
        ordinaryHypergeometric a (b:ℂ) ((b:ℂ)+(d:ℂ)) z := by
  rw [← beta_convolution a (b:ℂ) hb hd hz]
  apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
  intro u hu
  dsimp only
  rw [binomial hb (show ‖z*(u:ℂ)‖<1 from by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hu.1]
    exact (mul_le_of_le_one_right (norm_nonneg _) hu.2.le).trans_lt hz)]

end
end jacobi.Reference.Hypergeometric
