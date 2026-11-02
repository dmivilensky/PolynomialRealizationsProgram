import jacobi.Reference.NormRecurrence
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-!
Article: jacobi, Appendix C.1 (negative-energy bounds).
The genuine real Jacobi weight integral is evaluated by the community
Beta--Gamma identity. The real/complex power identification includes
the singular endpoint exponents throughout alpha,beta>-1.
Source: Euler's Beta integral, proved in mathlib's Gamma.Beta.
Use: evaluates the genuine degree-zero norm at every shifted parameter in the exact reference norm recurrence.
-/
namespace jacobi.Reference
noncomputable section
open Real Set MeasureTheory
set_option backward.isDefEq.respectTransparency false

/-- The literal real Jacobi weight integral has exactly Euler's Gamma quotient throughout its convergent parameter range.
Use: evaluates the genuine degree-zero norm at every shifted parameter in the exact reference norm recurrence.
Article: jacobi, Lemma C.1.
Source: Euler's Beta--Gamma identity, Complex.betaIntegral_eq_Gamma_mul_div.
Proof: embed the actual real integral in the complex field, identify the
nonnegative-base real powers with the community complex powers, apply
the proved Beta--Gamma identity and return to the real field. -/
theorem jacobi_weight_integral {a b : ℝ} (ha : -1<a) (hb : -1<b) :
    (∫ x in (0:ℝ)..1,jacobi.Jacobi.weight a b x)=
      Real.Gamma (a+1)*Real.Gamma (b+1)/Real.Gamma (a+b+2) := by
  -- Convergence of the original singular weight was established independently in Jacobi.Weight.
  apply Complex.ofReal_injective
  rw [← intervalIntegral.integral_ofReal]
  have hid : (∫ x in (0:ℝ)..1,(jacobi.Jacobi.weight a b x:ℂ))=
      Complex.betaIntegral ((a+1:ℝ):ℂ) ((b+1:ℝ):ℂ) := by
    unfold Complex.betaIntegral
    apply intervalIntegral.integral_congr
    intro x hx
    have hx : x∈Icc (0:ℝ) 1 := by simpa only [uIcc_of_le (by norm_num : (0:ℝ)≤1)] using hx
    have hA : ((a+1:ℝ):ℂ)-1=(a:ℂ) := by push_cast; ring
    have hB : ((b+1:ℝ):ℂ)-1=(b:ℂ) := by push_cast; ring
    rw [hA,hB]
    change (jacobi.Jacobi.weight a b x:ℂ)=(x:ℂ)^(a:ℂ)*(1-(x:ℂ))^(b:ℂ)
    rw [show (1:ℂ)-(x:ℂ)=((1-x:ℝ):ℂ) by push_cast; rfl,jacobi.Jacobi.weight,Complex.ofReal_mul,
      Complex.ofReal_cpow hx.1,Complex.ofReal_cpow (sub_nonneg.mpr hx.2)]
  rw [hid,Complex.betaIntegral_eq_Gamma_mul_div _ _ (by simp only [Complex.ofReal_re]; linarith)
    (by simp only [Complex.ofReal_re]; linarith)]
  have hsum : ((a+1:ℝ):ℂ)+((b+1:ℝ):ℂ)=((a+b+2:ℝ):ℂ) := by push_cast; ring
  rw [hsum]
  simp only [Complex.Gamma_ofReal,Complex.ofReal_mul,Complex.ofReal_div]

/-- The actual degree-zero Jacobi norm is the convergent original Beta integral with its exact Gamma value.
Use: starts the fully analytic reference norm recurrence, without a separately assumed norm formula.
Article: jacobi, Lemma C.1.
Proof: the actual degree-zero shifted Jacobi polynomial is identically one; apply the proved original weight integral. -/
theorem jacobiNorm_zero {a b : ℝ} (ha : -1<a) (hb : -1<b) :
    jacobiNorm a b 0=Real.Gamma (a+1)*Real.Gamma (b+1)/Real.Gamma (a+b+2) := by
  have hp : jacobi.Jacobi.shiftedPolynomial a b 0=1 := by
    simp [jacobi.Jacobi.shiftedPolynomial,jacobi.Jacobi.coefficient_zero]
  simpa only [jacobiNorm,hp,Polynomial.eval_one,one_pow,mul_one] using jacobi_weight_integral ha hb

end
end jacobi.Reference
