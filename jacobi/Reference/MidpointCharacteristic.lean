import jacobi.Reference.MidpointFormula

/-!
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
The product of the actual reference midpoint value and actual spatial
slope is exactly the printed reference characteristic with its original
constant kappa=2*pi^2*A(gamma). No arbitrary entire factor is introduced.
Source: Legendre's duplication formula for the Gamma function.
Use: pairs the four actual midpoint Gamma factors in wave_midpoint_characteristic.
-/
namespace jacobi.Reference
noncomputable section
open Real Set _root_.Complex
set_option backward.isDefEq.respectTransparency false

/-- Reciprocal Gamma duplication holds at every complex argument, including all Gamma poles.
Use: pairs the four actual midpoint Gamma factors in wave_midpoint_characteristic.
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
Source: Legendre's duplication formula, DLMF 5.5.5, already proved in mathlib.
Proof: invert the globally valid community duplication identity and
reverse the exponent 1-x. The square root of pi is genuinely nonzero;
no Gamma factor is divided out, so every pole remains covered. -/
theorem reciprocalGamma_duplication (x : ℂ) :
    (Complex.Gamma (x/2))⁻¹*(Complex.Gamma ((x+1)/2))⁻¹=
      (Complex.Gamma x)⁻¹*(2:ℂ)^(x-1)/(Real.sqrt Real.pi:ℂ) := by
  rw [show (x+1)/2=x/2+1/2 by ring,← mul_inv,Complex.Gamma_mul_Gamma_add_half,
    show 2*(x/2)=x by ring,mul_inv,mul_inv,← Complex.cpow_neg,
    show -(1-x)=x-1 by ring]
  ring

/-- The source characteristic normalization kappa is exactly 2^(2*gamma) times the square of the original midpoint scalar.
Use: converts the duplication prefactor in wave_midpoint_characteristic to the original independently evaluated norm constant.
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
Proof: use the proved genuine norm constant, the physical Jacobi
coordinate scale and positive-base power laws. The pi exponents add
to one; every cancelled scalar is strictly positive. -/
theorem midpointScalar_normalization {a : ℝ} (ha : -1<a) :
    2*Real.pi^2*normConstant a=(2:ℝ)^(2*gamma a)*midpointScalar a^2 := by
  -- The scalar A(gamma) is the one already identified with the original squared integral norms.
  have hp : Real.pi^(2*gamma a)*(Real.pi^(1/2-gamma a))^2=Real.pi := by
    rw [← Real.rpow_two (Real.pi^(1/2-gamma a)),← Real.rpow_mul Real.pi_pos.le,
      ← Real.rpow_add Real.pi_pos,show 2*gamma a+(1/2-gamma a)*2=(1:ℝ) by ring,
      Real.rpow_one]
  rw [normConstant_eq ha,coordinateScale,midpointScalar,Real.div_rpow Real.pi_pos.le (by norm_num),mul_pow]
  field_simp
  have hp' : Real.pi^(2*gamma a)*(Real.pi^((1-2*gamma a)/2))^2=Real.pi := by
    rw [show (1-2*gamma a)/2=(1/2:ℝ)-gamma a by ring]
    exact hp
  linear_combination -Real.Gamma ((2*gamma a+1)/2)^2*hp'

/-- The product of the actual reference midpoint value and actual spatial slope equals the literal reference characteristic, with exactly the original kappa.
Use: supplies the exact midpoint factorization in Proposition C.2's reference comparison and the negative-axis normalization argument.
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
Source: the proved Gauss midpoint formulas and Legendre's Gamma duplication formula.
Proof: pair the four reciprocal Gamma factors by duplication at
gamma-lambda and gamma+lambda. Their powers of two combine independently
of frequency; the proved original scalar normalization gives kappa. -/
theorem wave_midpoint_characteristic {a : ℝ} (ha : -1<a) (omega : ℂ) :
    2*wave a omega (1/2)*waveSlope a omega (1/2)=
      ((2*Real.pi^2*normConstant a:ℝ):ℂ)*characteristicGamma a (omega/(Real.pi:ℂ)) := by
  -- Both actual midpoint functions are evaluated before their Gamma factors are regrouped.
  let g : ℂ := (gamma a:ℂ)
  let l : ℂ := omega/(Real.pi:ℂ)
  have hm := reciprocalGamma_duplication (g-l)
  have hp := reciprocalGamma_duplication (g+l)
  have hmarg : (g-l+1)/2=(g+1-l)/2 := by ring
  have hparg : (g+l+1)/2=(g+1+l)/2 := by ring
  rw [hmarg] at hm
  rw [hparg] at hp
  have hpow : (2:ℂ)^(g-l-1)*(2:ℂ)^(g+l-1)=
      (((2:ℝ)^(2*gamma a)/4:ℝ):ℂ) := by
    rw [← Complex.cpow_add _ _ (by norm_num : (2:ℂ)≠0),
      show g-l-1+(g+l-1)=2*g-2 by ring]
    dsimp [g]
    rw [show 2*(gamma a:ℂ)-2=((2*gamma a-2:ℝ):ℂ) by push_cast; ring,
      show (2:ℂ)=((2:ℝ):ℂ) by norm_num,
      ← Complex.ofReal_cpow (by norm_num : (0:ℝ)≤2),
      Real.rpow_sub (by norm_num : (0:ℝ)<2),Real.rpow_two]
    norm_num
  have hsqrt : (Real.sqrt Real.pi:ℂ)^2=(Real.pi:ℂ) := by
    rw [← Complex.ofReal_pow,Real.sq_sqrt Real.pi_pos.le]
  rw [wave_midpoint_formula ha,waveSlope_midpoint_formula ha,
    midpointScalar_normalization ha,characteristicGamma]
  change 2*((midpointScalar a:ℂ)*(Complex.Gamma ((g+1-l)/2))⁻¹*(Complex.Gamma ((g+1+l)/2))⁻¹)*
    (2*(Real.pi:ℂ)*(midpointScalar a:ℂ)*(Complex.Gamma ((g-l)/2))⁻¹*(Complex.Gamma ((g+l)/2))⁻¹)=_
  calc
    _ = 4*(Real.pi:ℂ)*(midpointScalar a:ℂ)^2*
        ((Complex.Gamma ((g-l)/2))⁻¹*(Complex.Gamma ((g+1-l)/2))⁻¹)*
          ((Complex.Gamma ((g+l)/2))⁻¹*(Complex.Gamma ((g+1+l)/2))⁻¹) := by ring
    _ = _ := by
      rw [hm,hp]
      have hscalar : 4*(Real.pi:ℂ)*
          ((2:ℂ)^(g-l-1)/(Real.sqrt Real.pi:ℂ))*
            ((2:ℂ)^(g+l-1)/(Real.sqrt Real.pi:ℂ))=
            (((2:ℝ)^(2*gamma a):ℝ):ℂ) := by
        calc
          _ = 4*((2:ℂ)^(g-l-1)*(2:ℂ)^(g+l-1))*
              ((Real.pi:ℂ)/(Real.sqrt Real.pi:ℂ)^2) := by ring
          _ = _ := by
            rw [hpow,hsqrt,div_self (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)]
            push_cast
            ring
      change 4*(Real.pi:ℂ)*(midpointScalar a:ℂ)^2*
        ((Complex.Gamma (g-l))⁻¹*(2:ℂ)^(g-l-1)/(Real.sqrt Real.pi:ℂ))*
          ((Complex.Gamma (g+l))⁻¹*(2:ℂ)^(g+l-1)/(Real.sqrt Real.pi:ℂ))=
            (((2:ℝ)^(2*gamma a)*midpointScalar a^2:ℝ):ℂ)*
              ((Complex.Gamma (g-l))⁻¹*(Complex.Gamma (g+l))⁻¹)
      push_cast
      linear_combination (midpointScalar a:ℂ)^2*
        (Complex.Gamma (g-l))⁻¹*(Complex.Gamma (g+l))⁻¹*hscalar

end
end jacobi.Reference
