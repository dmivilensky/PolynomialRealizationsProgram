import jacobi.Young.Hyperbolic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
Article: jacobi, Equation (3.3) (exact U density and full spectrum).
The exponential convolution of the literal equality profile is evaluated
exactly. This verifies the equality candidate's second spectral moment and
its Euler equation without numerical integration or an assumed convolution.
Source: whole-line Green convolution split into its two exponential half-lines.
Use: differentiates the weighted primitives of sech^4 on the two half-lines.
-/
namespace jacobi.Young
noncomputable section
open MeasureTheory Real Set Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- Exponential and hyperbolic coordinates obey the exact conjugacy identity.
Use: differentiates the weighted primitives of sech^4 on the two half-lines.
Article: jacobi, Equation (3.3) (exact U density and full spectrum).
Proof: exp(x)=cosh(x)+sinh(x), divided by positive cosh(x), then squared. -/
theorem exp_sech_sq (x : ℝ) : Real.exp (2*x)*sech x^2 = (1+Real.tanh x)^2 := by
  have h' := congrArg (fun y : ℝ => y^2) (exp_mul_sech x)
  simpa only [mul_pow, ← Real.exp_nat_mul, Nat.cast_ofNat] using h'

/-- Left weighted sech^4 is integrable up to every finite endpoint.
Use: licenses the left improper fundamental theorem in the convolution calculation.
Article: jacobi, Equation (3.3) (exact U density and full spectrum).
Proof: sech≤1, so the integrand is dominated by exp(2x) on the left half-line. -/
theorem weighted_left_integrable (a : ℝ) :
    IntegrableOn (fun y => Real.exp (2*y)*sech y^4) (Iic a) := by
  apply (integrableOn_exp_mul_Iic (by norm_num : (0 : ℝ)<2) a).mono'
  · exact ((continuous_exp.comp (continuous_const.mul continuous_id)).mul
      ((Real.continuous_cosh.inv₀ (fun x => (Real.cosh_pos x).ne')).pow 4)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have hs : sech y ≤ 1 := inv_le_one_of_one_le₀ (Real.one_le_cosh y)
      exact mul_le_of_le_one_right (Real.exp_pos _).le (pow_le_one₀ (sech_pos y).le hs)

/-- The exact weighted primitive at the left endpoint of the convolution split.
Use: evaluates the left half of exp(-2|x-y|)*sech^4(y).
Article: jacobi, Equation (3.3) (exact U density and full spectrum).
Proof: (1+tanh(x))^3/3 has the required derivative and tends to zero at minus infinity. -/
theorem weighted_left_integral (x : ℝ) :
    (∫ y in Iic x, Real.exp (2*y)*sech y^4) = (1+Real.tanh x)^3/3 := by
  -- The derivative identity retains the exponential weight exactly.
  have hd (y : ℝ) : HasDerivAt (fun z => (1+Real.tanh z)^3/3)
      (Real.exp (2*y)*sech y^4) y := by
    convert (((tanh_derivative y).const_add 1).pow 3).div_const 3 using 1
    have he := exp_sech_sq y
    nlinarith [congrArg (fun r : ℝ => r*sech y^2) he]
  have hb := ((tanh_atBot.const_add 1).pow 3).div_const 3
  have h := integral_Iic_of_hasDerivAt_of_tendsto' (fun y _ => hd y) (weighted_left_integrable x) hb
  norm_num at h
  exact h

/-- The full exponential convolution of the Young equality profile.
Use: proves the actual attaining second moment G_2(sech^4)=32/45.
Article: jacobi, Equation (3.3) (exact U density and full spectrum).
Proof: split at x, reflect the right half to the left half, evaluate the two
weighted primitives and simplify the hyperbolic identities. -/
theorem sech_four_convolution (x : ℝ) :
    (∫ y, Real.exp (-2*|x-y|)*sech y^4) = (2/3 : ℝ)*sech x^2 := by
  -- Both pieces are integrable since the exponential kernel is bounded by one.
  have hi : Integrable (fun y => Real.exp (-2*|x-y|)*sech y^4) := by
    have hfour : Integrable (fun y : ℝ => sech y^4) volume := by simpa using sech_even_integrable 1
    refine hfour.mono' (f := fun y : ℝ => Real.exp (-2*|x-y|)*sech y^4) ?_ ?_
    · exact ((continuous_exp.comp ((continuous_const.mul ((continuous_const.sub continuous_id).abs)))).mul
        ((Real.continuous_cosh.inv₀ (fun z => (Real.cosh_pos z).ne')).pow 4)).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact mul_le_of_le_one_left (by positivity) (Real.exp_le_one_iff.mpr (by nlinarith [abs_nonneg (x-y)]))
  have hl (t : ℝ) : (∫ y in Iic t, Real.exp (-2*|t-y|)*sech y^4) =
      Real.exp (-2*t)*(1+Real.tanh t)^3/3 := by
    calc
      _ = Real.exp (-2*t)*(∫ y in Iic t, Real.exp (2*y)*sech y^4) := by
        rw [← integral_const_mul]
        apply setIntegral_congr_fun measurableSet_Iic
        intro y hy
        dsimp only
        rw [abs_of_nonneg (sub_nonneg.mpr hy), ← mul_assoc, ← Real.exp_add]
        congr 2
        ring
      _ = _ := by rw [weighted_left_integral]; ring
  have hr : (∫ y in Ioi x, Real.exp (-2*|x-y|)*sech y^4) =
      Real.exp (2*x)*(1-Real.tanh x)^3/3 := by
    have hn := integral_comp_neg_Iic (-x) (fun y => Real.exp (-2*|x-y|)*sech y^4)
    simp only [neg_neg] at hn
    rw [← hn]
    have h : (fun y => Real.exp (-2*|x- -y|)*sech (-y)^4) =
        (fun y => Real.exp (-2*|(-x)-y|)*sech y^4) := by
      funext y
      rw [show |x- -y| = |(-x)-y| by rw [← abs_neg]; congr 1; ring]
      simp [sech]
    rw [h]
    have hlx := hl (-x)
    rw [show -2*(-x) = 2*x by ring] at hlx
    simpa only [Real.tanh_neg, sub_eq_add_neg] using hlx
  rw [← integral_add_compl measurableSet_Iic hi, hl x]
  have hs : (Iic x)ᶜ = Ioi x := compl_Iic
  rw [hs, hr]
  have hp := exp_sech_sq x
  have hm := exp_sech_sq (-x)
  have hsneg : sech (-x) = sech x := by simp [sech]
  simp only [mul_neg, hsneg, Real.tanh_neg] at hm
  have hn : sech x ≠ 0 := (sech_pos x).ne'
  have he1 : Real.exp (2*x) = (1+Real.tanh x)^2/sech x^2 :=
    (eq_div_iff (pow_ne_zero 2 hn)).mpr hp
  have he2 : Real.exp (-2*x) = (1-Real.tanh x)^2/sech x^2 := by
    apply (eq_div_iff (pow_ne_zero 2 hn)).mpr
    rw [show -2*x = -(2*x) by ring, sub_eq_add_neg]
    exact hm
  rw [he1, he2]
  field_simp [hn]
  rw [show sech x^4 = (sech x^2)^2 by ring, sech_sq]
  ring

end
end jacobi.Young
