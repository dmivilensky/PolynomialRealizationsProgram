import jacobi.Reference.SecondSummation
import jacobi.Reference.HypergeometricDerivative
import jacobi.Reference.CharacteristicNorming
import jacobi.Reference.WaveDerivatives

/-!
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
The exact reciprocal-Gamma formulas are proved for the original reference
wave and its genuine spatial derivative, at every complex frequency.
All constants retain the normalization of the original selected branch.
Source: Gauss's second summation theorem, DLMF 15.4.28, proved in
SecondSummation, and its derivative formula, DLMF 15.5.1, proved in
HypergeometricDerivative.
Use: gives the genuine normalization in wave_midpoint_formula and waveSlope_midpoint_formula and identifies their characteristic product.
-/
namespace jacobi.Reference
noncomputable section
open Real Set _root_.Complex
set_option backward.isDefEq.respectTransparency false

/-- The exact common scalar in the two original midpoint reference formulas.
Use: gives the genuine normalization in wave_midpoint_formula and waveSlope_midpoint_formula and identifies their characteristic product.
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
-/
def midpointScalar (a : ℝ) : ℝ :=
  Real.pi^(1/2-gamma a)*Real.Gamma (gamma a+1/2)

/-- The original physical prefactor and coordinate have their exact midpoint values.
Use: reduces the actual reference wave and slope to the Gauss second summation formulas.
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
Proof: sin(pi/2)=1 and cos(pi/2)=0; the positive inverse-pi power is pi^(-gamma). -/
theorem midpoint_coordinates (a : ℝ) :
    weight a (1/2)=Real.pi^(-gamma a) ∧ coordinate (1/2)=1/2 ∧
      weightLogSlope a (1/2)=0 ∧ coordinateSlope (1/2)=Real.pi/2 := by
  simp only [weight,coordinate,weightLogSlope,coordinateSlope]
  rw [show Real.pi*(1/2:ℝ)=Real.pi/2 by ring,Real.sin_pi_div_two,Real.cos_pi_div_two]
  simp [Real.inv_rpow Real.pi_pos.le,Real.rpow_neg Real.pi_pos.le]

/-- The common midpoint scalar is the exact original weight times sqrt(pi) times Gamma(gamma+1/2).
Use: fixes the scalar when the original midpoint wave is evaluated by second_summation.
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
Proof: combine the positive-base pi powers -gamma and 1/2. -/
theorem midpointScalar_eq (a : ℝ) :
    midpointScalar a=Real.pi^(-gamma a)*Real.sqrt Real.pi*Real.Gamma (gamma a+1/2) := by
  rw [midpointScalar,Real.sqrt_eq_rpow,← Real.rpow_add Real.pi_pos]
  congr 2
  ring

/-- The actual reference wave at the midpoint has exactly the article's reciprocal-Gamma formula, including every complex spectral frequency.
Use: proves the exact reference characteristic product and identifies its two midpoint zero classes.
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
Source: Gauss's second summation theorem, DLMF 15.4.28, proved here in SecondSummation.
Proof: insert the exact physical midpoint coordinate in the original wave and apply the proved entire second summation formula. -/
theorem wave_midpoint_formula {a : ℝ} (ha : -1<a) (omega : ℂ) :
    wave a omega (1/2)=(midpointScalar a:ℂ)*
      (Complex.Gamma (((gamma a:ℂ)+1-omega/(Real.pi:ℂ))/2))⁻¹*
        (Complex.Gamma (((gamma a:ℂ)+1+omega/(Real.pi:ℂ))/2))⁻¹ := by
  have hg : 0<gamma a := by linarith [(parameters ha).1]
  rw [wave,waveCore,(midpoint_coordinates a).1,(midpoint_coordinates a).2.1,
    Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat,Hypergeometric.second_summation hg,
    midpointScalar_eq]
  push_cast
  rw [← Complex.Gamma_ofReal]
  push_cast
  ring

/-- The actual spatial midpoint slope has the article's exact reciprocal-Gamma formula for every complex frequency.
Use: proves the reference characteristic product and its Neumann midpoint zero set, using the genuine derivative of the original f.
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
Source: DLMF 15.5.1 and 15.4.28, both proved here for the actual community functions.
Proof: the prefactor's midpoint logarithmic derivative vanishes.
Differentiate the genuine Gauss function, apply second summation at
gamma+1, and use the globally valid reciprocal-Gamma recurrence.
This last recurrence includes Gamma poles, so all complex frequencies
and every reference eigenvalue are covered by the same formula. -/
theorem waveSlope_midpoint_formula {a : ℝ} (ha : -1<a) (omega : ℂ) :
    waveSlope a omega (1/2)=2*(Real.pi:ℂ)*(midpointScalar a:ℂ)*
      (Complex.Gamma (((gamma a:ℂ)-omega/(Real.pi:ℂ))/2))⁻¹*
        (Complex.Gamma (((gamma a:ℂ)+omega/(Real.pi:ℂ))/2))⁻¹ := by
  -- The original slope reduces to the true hypergeometric derivative at the midpoint.
  have hg : 0<gamma a := by linarith [(parameters ha).1]
  let g : ℂ := (gamma a:ℂ)
  let l : ℂ := omega/(Real.pi:ℂ)
  have hc : 0<(g+1/2).re := by dsimp [g]; norm_num; linarith
  have hc0 : g+1/2≠0 := by intro h; rw [h,zero_re] at hc; linarith
  have hc2 : 2*g+1≠0 := by
    rw [show 2*g+1=2*(g+1/2) by ring]
    exact mul_ne_zero (by norm_num) hc0
  have hga : 0<gamma a+1 := by linarith
  have hs := Hypergeometric.second_summation hga l
  push_cast at hs
  have hΓ : Complex.Gamma (g+1+1/2)=(g+1/2)*Complex.Gamma (g+1/2) := by
    rw [show g+1+1/2=g+1/2+1 by ring,Complex.Gamma_add_one _ hc0]
  have hm := Complex.one_div_Gamma_eq_self_mul_one_div_Gamma_add_one ((g-l)/2)
  have hp := Complex.one_div_Gamma_eq_self_mul_one_div_Gamma_add_one ((g+l)/2)
  have hmarg : (g+1+1-l)/2=(g-l)/2+1 := by ring
  have hparg : (g+1+1+l)/2=(g+l)/2+1 := by ring
  rw [waveSlope,waveCore,(midpoint_coordinates a).1,(midpoint_coordinates a).2.1,
    (midpoint_coordinates a).2.2.1,(midpoint_coordinates a).2.2.2,
    Complex.ofReal_zero,zero_mul,zero_add]
  push_cast
  change ((Real.pi^(-gamma a):ℝ):ℂ)*((Real.pi:ℂ)/2*
    deriv (ordinaryHypergeometric (g-l) (g+l) (g+1/2)) (1/2:ℂ))=_
  rw [Hypergeometric.derivative_shift hc (by norm_num)]
  rw [show (g-l)+1=(g+1)-l by ring,show (g+l)+1=(g+1)+l by ring,
    show g+1/2+1=(g+1)+1/2 by ring,hs]
  change ((Real.pi^(-gamma a):ℝ):ℂ)*((Real.pi:ℂ)/2*
    ((g-l)*(g+l)/(g+1/2)*((Real.sqrt Real.pi:ℂ)*Complex.Gamma (g+1+1/2)*
      (Complex.Gamma ((g+1+1-l)/2))⁻¹*(Complex.Gamma ((g+1+1+l)/2))⁻¹)))=_
  rw [hΓ,hmarg,hparg,midpointScalar_eq]
  push_cast
  have hrealΓ : (Real.Gamma (gamma a+1/2):ℂ)=Complex.Gamma (g+1/2) := by
    rw [← Complex.Gamma_ofReal]; push_cast; rfl
  rw [hrealΓ]
  have hm' : (Complex.Gamma ((g-l)/2))⁻¹=(g-l)/2*(Complex.Gamma ((g-l)/2+1))⁻¹ := by simpa only [one_div] using hm
  have hp' : (Complex.Gamma ((g+l)/2))⁻¹=(g+l)/2*(Complex.Gamma ((g+l)/2+1))⁻¹ := by simpa only [one_div] using hp
  rw [hm',hp']
  field_simp [hc2]

end
end jacobi.Reference
