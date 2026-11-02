import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.MeasureTheory.Integral.Asymptotics
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
Article: jacobi, Section 3.2 (sharp Young inequality).
Source: hyperbolic calculus and the whole-line fundamental theorem in mathlib.
Use: sech^4 defines the Young equality densities and the distinguished density m_U.
-/
namespace jacobi.Young
noncomputable section
open MeasureTheory Real Filter Asymptotics
open scoped Topology

/-- The hyperbolic secant, used for the literal equality profiles.
Use: sech^4 defines the Young equality densities and the distinguished density m_U.
Article: jacobi, Section 3.2 (sharp Young inequality).
-/
def sech (x : ℝ) : ℝ := (Real.cosh x)⁻¹

/-- Hyperbolic secant is positive everywhere.
Use: fixes all square-root and real-power branches in the equality profiles.
Article: jacobi, Equation (3.3) (exact U density and full spectrum).
Proof: real hyperbolic cosine is strictly positive. -/
theorem sech_pos (x : ℝ) : 0 < sech x := inv_pos.mpr (Real.cosh_pos x)

/-- Hyperbolic secant is even.
Use: reflects the equality profiles and the two weighted primitives in the full m_U spectral calculation.
Article: jacobi, Equation (3.3) (exact U density and full spectrum).
Proof: hyperbolic cosine is even and inversion preserves equality. -/
theorem sech_neg (x : ℝ) : sech (-x)=sech x := by simp [sech]

/-- Exponential and hyperbolic coordinates obey the exact unsquared identity.
Use: computes the exponential convolution of the Young profiles and every sine eigenfunction of m_U.
Article: jacobi, Equation (3.3) (exact U density and full spectrum).
Proof: exp(x)=cosh(x)+sinh(x), divided by the positive hyperbolic cosine. -/
theorem exp_mul_sech (x : ℝ) : Real.exp x*sech x=1+Real.tanh x := by
  rw [sech,Real.tanh_eq_sinh_div_cosh,← Real.cosh_add_sinh]
  field_simp [(Real.cosh_pos x).ne']

/-- The basic identity relating the profile to its hyperbolic coordinate.
Use: computes derivatives and antiderivatives of all equality-profile integrands.
Article: jacobi, Equation (3.3) (exact U density and full spectrum).
Proof: divide cosh^2-sinh^2=1 by the nonzero square of cosh. -/
theorem sech_sq (x : ℝ) : sech x^2 = 1-Real.tanh x^2 := by
  rw [sech, Real.tanh_eq_sinh_div_cosh]
  field_simp [(Real.cosh_pos x).ne']
  nlinarith [Real.cosh_sq_sub_sinh_sq x]

/-- The hyperbolic coordinate has derivative sech^2.
Use: supplies exact antiderivatives of sech^2, sech^4 and sech^6.
Article: jacobi, Equation (3.3) (exact U density and full spectrum).
Proof: differentiate sinh/cosh and use the hyperbolic square identity. -/
theorem tanh_derivative (x : ℝ) : HasDerivAt Real.tanh (sech x^2) x := by
  have h := (Real.hasDerivAt_sinh x).div (Real.hasDerivAt_cosh x) (Real.cosh_pos x).ne'
  convert h using 1
  · exact funext Real.tanh_eq_sinh_div_cosh
  · rw [sech]
    field_simp [(Real.cosh_pos x).ne']
    nlinarith [Real.cosh_sq_sub_sinh_sq x]

/-- The hyperbolic coordinate tends to one at the positive end.
Use: evaluates the endpoint values of the equality-profile antiderivatives.
Article: jacobi, Equation (3.3) (exact U density and full spectrum).
Proof: express tanh as (1-exp(-x)^2)/(1+exp(-x)^2) and pass to the limit. -/
theorem tanh_atTop : Tendsto Real.tanh atTop (𝓝 1) := by
  -- Dividing the exponential formula by exp(x) leaves a parameter tending to zero.
  have he (x : ℝ) : Real.tanh x =
      (1-Real.exp (-x)^2)/(1+Real.exp (-x)^2) := by
    rw [Real.tanh_eq, Real.exp_neg]
    field_simp
  have h := ((tendsto_const_nhds (x := (1 : ℝ))).sub (Real.tendsto_exp_neg_atTop_nhds_zero.pow 2)).div
    ((tendsto_const_nhds (x := (1 : ℝ))).add (Real.tendsto_exp_neg_atTop_nhds_zero.pow 2)) (by norm_num)
  change Tendsto (fun x : ℝ => (1-Real.exp (-x)^2)/(1+Real.exp (-x)^2)) atTop
    (𝓝 ((1-0^2)/(1+0^2) : ℝ)) at h
  simpa only [← he, zero_pow (by decide : 2 ≠ 0), sub_zero, add_zero, div_one] using h

/-- The hyperbolic coordinate tends to minus one at the negative end.
Use: evaluates the other endpoint in the whole-line integration formulas.
Article: jacobi, Equation (3.3) (exact U density and full spectrum).
Proof: use oddness and the already proved positive-end limit. -/
theorem tanh_atBot : Tendsto Real.tanh atBot (𝓝 (-1)) := by
  have h := (tanh_atTop.comp tendsto_neg_atBot_atTop).neg
  simpa only [Function.comp_def, Real.tanh_neg, neg_neg] using h

/-- A continuous even derivative with a finite primitive limit is globally integrable.
Use: proves integrability of the hyperbolic powers without assuming their integral values.
Article: jacobi, Equation (3.3) (exact U density and full spectrum).
Source: mathlib, nonnegative derivative integration and symmetry of Lebesgue measure.
Proof: monotonicity gives integrability at the positive end; evenness and local
integrability give integrability on the full real line. -/
theorem integrable_even_derivative {f g : ℝ → ℝ} {a : ℝ}
    (hf : Continuous f) (hpos : ∀ x, 0 ≤ f x) (heven : ∀ x, f (-x)=f x)
    (hd : ∀ x, HasDerivAt g (f x) x) (ht : Tendsto g atTop (𝓝 a)) : Integrable f := by
  have hi : IntegrableOn f (Set.Ioi 0) :=
    integrableOn_Ioi_deriv_of_nonneg' (fun x _ => hd x) (fun x _ => hpos x) ht
  exact hf.locallyIntegrable.integrable_of_isBigO_atTop_of_norm_isNegInvariant
    (Filter.Eventually.of_forall (fun x => by simp [Function.comp_def, heven]))
    (isBigO_refl f atTop) ⟨Set.Ioi 0, Ioi_mem_atTop 0, hi⟩

/-- sech^2 is integrable on the full line.
Use: its higher even powers are dominated by it and hence integrable too.
Article: jacobi, Section 3.2 (sharp Young inequality).
Proof: tanh is a finite-limit primitive and sech^2 is continuous, even and positive. -/
theorem sech_sq_integrable : Integrable (fun x => sech x^2) := by
  apply integrable_even_derivative (g := Real.tanh) (a := 1)
  · exact (Real.continuous_cosh.inv₀ (fun x => (Real.cosh_pos x).ne')).pow 2
  · intro x
    exact sq_nonneg _
  · intro x
    simp [sech]
  · exact tanh_derivative
  · exact tanh_atTop

/-- Every positive even power of sech is integrable.
Use: licenses exact mass and energy calculations for all Young equality profiles.
Article: jacobi, Equation (3.3) (exact U density and full spectrum).
Proof: 0<sech≤1, so each higher positive even power is bounded by sech^2. -/
theorem sech_even_integrable (n : ℕ) : Integrable (fun x => sech x^(2*(n+1))) := by
  -- Factor off sech²; every remaining even power is bounded by one.
  apply sech_sq_integrable.mono'
  · exact ((Real.continuous_cosh.inv₀ (fun x => (Real.cosh_pos x).ne')).pow _).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (sech_pos x).le _)]
      have hs : sech x ≤ 1 := by rw [sech]; exact inv_le_one_of_one_le₀ (Real.one_le_cosh x)
      have hp : sech x^(2*n) ≤ 1 := pow_le_one₀ (sech_pos x).le hs
      calc
        _ = sech x^2 * sech x^(2*n) := by rw [← pow_add]; congr 1; omega
        _ ≤ _ := mul_le_of_le_one_right (sq_nonneg _) hp

/-- The exact root-mass integral of the Young profile.
Use: shows rootMass(m_U)=1.
Article: jacobi, Equation (3.3) (exact U density and full spectrum).
Proof: integrate the derivative of tanh between its limits -1 and 1. -/
theorem integral_sech_sq : (∫ x, sech x^2) = 2 := by
  have h := integral_of_hasDerivAt_of_tendsto tanh_derivative sech_sq_integrable tanh_atBot tanh_atTop
  norm_num at h ⊢
  exact h

/-- The exact mass integral of the Young equality profile.
Use: shows mass(m_U)=1/3 and fixes the mass threshold in the Young regime.
Article: jacobi, Equation (3.3) (exact U density and full spectrum).
Proof: tanh-tanh^3/3 has derivative sech^4; evaluate its limits at both ends. -/
theorem integral_sech_four : (∫ x, sech x^4) = 4/3 := by
  -- The polynomial primitive is differentiated before applying the improper FTC.
  have hd (x : ℝ) : HasDerivAt (fun y => Real.tanh y-Real.tanh y^3/3) (sech x^4) x := by
    convert (tanh_derivative x).sub (((tanh_derivative x).pow 3).div_const 3) using 1
    rw [show sech x^4 = (sech x^2)^2 by ring, sech_sq]
    ring
  have hb := tanh_atBot.sub ((tanh_atBot.pow 3).div_const 3)
  have ht := tanh_atTop.sub ((tanh_atTop.pow 3).div_const 3)
  have h := integral_of_hasDerivAt_of_tendsto hd (by simpa using sech_even_integrable 1) hb ht
  norm_num at h ⊢
  exact h

/-- The exact energy integral of the Young equality profile.
Use: shows energy(m_U)=2/15.
Article: jacobi, Equation (3.3) (exact U density and full spectrum).
Proof: differentiate tanh-(2/3)tanh^3+tanh^5/5 and evaluate the two limiting values. -/
theorem integral_sech_six : (∫ x, sech x^6) = 16/15 := by
  -- The cubic power of 1-tanh^2 is exactly the derivative of this primitive.
  have hd (x : ℝ) : HasDerivAt
      (fun y => Real.tanh y-(2/3:ℝ)*Real.tanh y^3+Real.tanh y^5/5) (sech x^6) x := by
    convert ((tanh_derivative x).sub (((tanh_derivative x).pow 3).const_mul (2/3:ℝ))).add
      (((tanh_derivative x).pow 5).div_const 5) using 1
    rw [show sech x^6 = (sech x^2)^3 by ring, sech_sq]
    ring
  have hb := (tanh_atBot.sub ((tanh_atBot.pow 3).const_mul (2/3:ℝ))).add ((tanh_atBot.pow 5).div_const 5)
  have ht := (tanh_atTop.sub ((tanh_atTop.pow 3).const_mul (2/3:ℝ))).add ((tanh_atTop.pow 5).div_const 5)
  have h := integral_of_hasDerivAt_of_tendsto hd (by simpa using sech_even_integrable 2) hb ht
  norm_num at h ⊢
  exact h

end
end jacobi.Young
