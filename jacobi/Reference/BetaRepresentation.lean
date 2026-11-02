import jacobi.Reference.SineIntegral
import jacobi.Reference.MehlerIntegral
import jacobi.Reference.Solutions

/-!
Article: jacobi, Appendix C.1 (negative-energy bounds).
The defining singular beta integral is identified with the previously
constructed reference wave and solution, at every complex frequency and
every original spatial point 0<=t<1. The beta normalization is the actual
positive integral, and every real power and Jacobian has its exact scale.
Source: Euler's beta integral and the Mehler--Dirichlet formula.
Use: wave_beta_integral and solution_beta_integral identify all previously constructed reference functions with this actual integral.
-/
namespace jacobi.Reference
noncomputable section
open Real Set MeasureTheory _root_.Complex
open Hypergeometric
set_option backward.isDefEq.respectTransparency false

/-- The literal normalized defining beta integral from the article, in its original physical variable.
Use: wave_beta_integral and solution_beta_integral identify all previously constructed reference functions with this actual integral.
Article: jacobi, Appendix C.1 (negative-energy bounds).
-/
def betaWave (a : ℝ) (omega : ℂ) (t : ℝ) : ℂ :=
  (betaNormalization (gamma a):ℂ)⁻¹*
    ((((Real.sin (Real.pi*t)/Real.pi)^(1-gamma a)):ℝ):ℂ)*
      ∫ s in (0:ℝ)..t,sineIntegrand (gamma a) t omega s

/-- The exact real scale in the normalized sine integral is its original sine-power reference weight.
Use: cancels the original beta normalization and all angular Jacobians in wave_beta_integral.
Article: jacobi, Appendix C.1 (negative-energy bounds).
Proof: the powers of two cancel, the two sine powers add to gamma,
and the pi powers give pi^(-gamma). All bases canceled here are
strictly positive actual real quantities. -/
theorem beta_scaling (g : ℝ) {s B : ℝ} (hs : 0<s) (hB : 0<B) :
    B⁻¹*(s/Real.pi)^(1-g)*((2*Real.pi^2)^(1-g)/Real.pi)*
      ((2:ℝ)^(g-1)*B*s^(2*g-1))=(s/Real.pi)^g := by
  -- Keep the algebra in the real field; only the finished identity is embedded into the complex-valued integral.
  have htwo : (2:ℝ)^(1-g)*(2:ℝ)^(g-1)=1 := by
    rw [← Real.rpow_add (by norm_num : (0:ℝ)<2),show 1-g+(g-1)=(0:ℝ) by ring,Real.rpow_zero]
  have hsin : s^(1-g)*s^(2*g-1)=s^g := by
    rw [← Real.rpow_add hs,show 1-g+(2*g-1)=g by ring]
  have hpi : Real.pi^(1-g)=Real.pi*(Real.pi^g)⁻¹ := by
    rw [Real.rpow_sub Real.pi_pos,Real.rpow_one,div_eq_mul_inv]
  rw [Real.div_rpow hs.le Real.pi_pos.le,
    Real.mul_rpow (by norm_num : (0:ℝ)≤2) (sq_nonneg _),
    ← Real.rpow_natCast_mul Real.pi_pos.le, Nat.cast_ofNat,
    show (2:ℝ)*(1-g)=(1-g)+(1-g) by ring,Real.rpow_add Real.pi_pos,
    Real.div_rpow hs.le Real.pi_pos.le]
  have hN := (Real.rpow_pos_of_pos Real.pi_pos (1-g)).ne'
  have hG := (Real.rpow_pos_of_pos Real.pi_pos g).ne'
  apply (eq_div_iff hG).mpr
  calc
    _ = (Real.pi^(1-g)/Real.pi)*(s^(1-g)*s^(2*g-1))*Real.pi^g*
        ((2:ℝ)^(1-g)*(2:ℝ)^(g-1))*(B⁻¹*B) := by
          field_simp [hB.ne',Real.pi_ne_zero,hN]
    _ = s^g := by rw [htwo,inv_mul_cancel₀ hB.ne',mul_one,mul_one,hsin,hpi]; field_simp

/-- The existing actual hypergeometric reference wave equals the literal defining beta integral with no unproved normalization premise.
Use: transfers genuine positive-weight integral estimates and negative-energy asymptotics to the same wave used by the GL construction.
Article: jacobi, Lemma C.1.
Proof: the original sine integral has its proved genuine convergence
and exact angular change of variables. The normalized Mehler identity
gives its actual Gauss function; beta_scaling identifies the outside
factor with the original weight. At t=0 both original objects vanish. -/
theorem wave_beta_integral {a : ℝ} (ha : -1<a) (omega : ℂ) {t : ℝ}
    (ht : t∈Ico (0:ℝ) 1) : wave a omega t=betaWave a omega t := by
  -- The equality is for the already defined wave, not for an auxiliary solution with stipulated integral properties.
  have hg : 0<gamma a := by linarith [(parameters ha).1]
  by_cases ht0 : t=0
  · subst t
    simp [betaWave,wave,(weight_properties ha).2.1]
  have ht' : t∈Ioo (0:ℝ) 1 := ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0),ht.2⟩
  have htheta : Real.pi*t∈Ioo (0:ℝ) Real.pi :=
    ⟨mul_pos Real.pi_pos ht'.1,by nlinarith [Real.pi_pos,ht'.2]⟩
  have hm := mehler_reference_identity hg htheta (omega/(Real.pi:ℂ))
  have hc := congrArg Complex.ofReal (beta_scaling (gamma a)
    (Real.sin_pos_of_pos_of_lt_pi htheta.1 htheta.2) (betaNormalization_pos hg))
  unfold betaWave
  rw [sine_integral_angular hg ht' omega,hm]
  unfold wave waveCore weight coordinate angularCoordinate
  push_cast at hc ⊢
  linear_combination -ordinaryHypergeometric ((gamma a:ℂ)-omega/(Real.pi:ℂ))
    ((gamma a:ℂ)+omega/(Real.pi:ℂ)) ((gamma a:ℂ)+1/2)
      ((1-Complex.cos ((Real.pi:ℂ)*(t:ℂ)))/2)*hc

/-- The actual reference solution at an arbitrary complex energy equals its defining beta integral for every chosen frequency with the prescribed square.
Use: all later positivity, domination and negative-energy comparisons apply directly to the original f(t,z).
Article: jacobi, Lemma C.1.
Proof: the already proved frequency-square independence identifies solution with wave; wave_beta_integral gives the exact defining integral. -/
theorem solution_beta_integral {a : ℝ} (ha : -1<a) {z omega : ℂ}
    (homega : omega^2=z-(jacobi.Jacobi.endpointCorrection a:ℂ)) {t : ℝ}
    (ht : t∈Ico (0:ℝ) 1) : solution a z t=betaWave a omega t := by
  rw [solution_eq_wave a homega,wave_beta_integral ha omega ht]

end
end jacobi.Reference
