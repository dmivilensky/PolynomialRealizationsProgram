import jacobi.Reference.BetaIntegral
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
Article: jacobi, Appendix C.1 (negative-energy bounds).
The normalizing B(gamma,gamma) is the literal original singular integral,
with its proved positive Gamma value. Legendre's duplication formula
evaluates the half-parameter beta factor in the actual angular integral.
Source: Euler's beta integral and Legendre's Gamma duplication formula.
Use: fixes the normalization of the literal sine-power integral without stipulating a Gamma quotient as its definition.
-/
namespace jacobi.Reference
noncomputable section
open Real Set MeasureTheory
set_option backward.isDefEq.respectTransparency false

/-- The original symmetric beta integral used in the article's defining reference solution.
Use: fixes the normalization of the literal sine-power integral without stipulating a Gamma quotient as its definition.
Article: jacobi, Appendix C.1 (negative-energy bounds).
-/
def betaNormalization (g : ℝ) : ℝ :=
  ∫ r in (0:ℝ)..1,jacobi.Jacobi.weight (g-1) (g-1) r

/-- The actual symmetric beta normalization has exactly its genuine Gamma quotient.
Use: matches the literal integral normalization with the independent hypergeometric formula in the beta identity.
Article: jacobi, Appendix C.1 (negative-energy bounds).
Source: Euler's beta--Gamma identity, already proved for the original singular Jacobi weight.
Proof: specialize the full weight-integral evaluation to the two positive equal beta parameters. -/
theorem betaNormalization_eq {g : ℝ} (hg : 0<g) :
    betaNormalization g=Real.Gamma g^2/Real.Gamma (2*g) := by
  rw [betaNormalization,jacobi_weight_integral (by linarith) (by linarith),
    show g-1+1=g by ring,show g-1+(g-1)+2=2*g by ring,pow_two]

/-- The original beta integral is strictly positive throughout its full convergent parameter range.
Use: every cancellation in the defining reference solution's normalization uses a genuine nonzero scalar.
Article: jacobi, Appendix C.1 (negative-energy bounds).
Proof: both actual positive-argument Gamma factors are strictly positive. -/
theorem betaNormalization_pos {g : ℝ} (hg : 0<g) : 0<betaNormalization g := by
  rw [betaNormalization_eq hg]
  exact div_pos (sq_pos_of_pos (Real.Gamma_pos_of_pos hg)) (Real.Gamma_pos_of_pos (by positivity))

/-- The genuine half-parameter beta factor equals the original symmetric beta normalization times the exact power of two.
Use: fixes every scalar in mehler_reference_identity and hence in the literal beta-integral identification of the actual f.
Article: jacobi, Appendix C.1 (negative-energy bounds).
Source: Legendre's Gamma duplication formula and Gamma(1/2)=sqrt(pi), both proved in mathlib.
Proof: multiply the actual duplication identity by the complementary
power of two; the exponents add to zero. The two resulting positive
Gamma quotients are then equal by exact cancellation. -/
theorem half_beta_normalization {g : ℝ} (hg : 0<g) :
    Real.Gamma (1/2)*Real.Gamma g/Real.Gamma (g+1/2)=
      (2:ℝ)^(2*g-1)*betaNormalization g := by
  -- The integral normalization was independently evaluated before the Gamma duplication scalar is used.
  rw [betaNormalization_eq hg,Real.Gamma_one_half_eq]
  have hG := (Real.Gamma_pos_of_pos hg).ne'
  have hH := (Real.Gamma_pos_of_pos (show 0<g+1/2 by linarith)).ne'
  have hD := (Real.Gamma_pos_of_pos (show 0<2*g by positivity)).ne'
  have hd := Real.Gamma_mul_Gamma_add_half g
  have hp : (2:ℝ)^(2*g-1)*(2:ℝ)^(1-2*g)=1 := by
    rw [← Real.rpow_add (by norm_num : (0:ℝ)<2),show 2*g-1+(1-2*g)=(0:ℝ) by ring,Real.rpow_zero]
  simp only [← mul_div_assoc]
  apply (div_eq_div_iff hH hD).mpr
  calc
    _ = Real.Gamma g*Real.Gamma (2*g)*Real.sqrt Real.pi := by ring
    _ = Real.Gamma g*Real.Gamma (2*g)*Real.sqrt Real.pi*
        ((2:ℝ)^(2*g-1)*(2:ℝ)^(1-2*g)) := by rw [hp,mul_one]
    _ = (2:ℝ)^(2*g-1)*Real.Gamma g*
        (Real.Gamma (2*g)*(2:ℝ)^(1-2*g)*Real.sqrt Real.pi) := by ring
    _ = _ := by rw [← hd]; ring

end
end jacobi.Reference
