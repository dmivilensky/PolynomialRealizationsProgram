import krylov.Functions.TrapezoidIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-!
Article: main_krylov, thm:Fexact, sharp smooth endpoint diagonal remainder.
Use: prove the 1/12 endpoint estimate under a Lipschitz third derivative, without
assuming a fourth derivative. The a.e. integration-by-parts infrastructure is imported.
Source: Appendix G, using mathlib's FTC for absolutely continuous functions.
-/

namespace krylov.Functions
noncomputable section
open Set MeasureTheory
open scoped NNReal Topology

/-- The derivative of the nonnegative endpoint correction kernel.
Article: main_krylov, thm:Fexact. Proof: differentiate the scalar polynomial. -/
theorem endpoint_kernel_hasDerivAt (t : ℝ) :
    HasDerivAt (fun t : ℝ => t ^ 2 * (1 - t)) (2 * t - 3 * t ^ 2) t := by
  convert! ((hasDerivAt_id t).pow 2).mul
    ((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)) using 1
  simp only [Pi.sub_apply, Pi.pow_apply, id_eq]
  ring

/-- The exact nonnegative endpoint kernel has integral 1/12.
Article: main_krylov, thm:Fexact. Proof: integrate its polynomial primitive. -/
theorem integral_endpoint_kernel : (∫ t in (0 : ℝ)..1, t ^ 2 * (1 - t)) = 1 / 12 := by
  have hd (t : ℝ) : HasDerivAt (fun t : ℝ => t ^ 3 / 3 - t ^ 4 / 4)
      (t ^ 2 * (1 - t)) t := by
    convert! (((hasDerivAt_id t).pow 3).div_const 3).sub
      (((hasDerivAt_id t).pow 4).div_const 4) using 1
    simp only [id_eq]
    ring
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t (_ : t ∈ uIcc (0 : ℝ) 1) => hd t)
    ((by fun_prop : Continuous (fun t : ℝ => t ^ 2 * (1 - t))).intervalIntegrable 0 1)
  norm_num at h ⊢
  exact h

/-- A Lipschitz third derivative gives the sharp corrected endpoint diagonal bound.
Article: main_krylov, thm:Fexact, the 1/12 term at x=b and lambda=1/2.
Proof: first derive the exact Peano-kernel integral. Then use imported absolutely
continuous integration by parts and the a.e. Lipschitz derivative norm bound. -/
theorem trapezoid_corrected_endpoint_bound (f f₁ f₂ f₃ : ℝ → ℝ)
    (h₁ : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt f (f₁ t) t)
    (h₂ : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt f₁ (f₂ t) t)
    (h₃ : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt f₂ (f₃ t) t)
    (L : ℝ≥0) (hL : LipschitzOnWith L f₃ (Icc 0 1)) :
    |f₁ 1 - f₁ 0 - 6 * trapezoidDefect f f₁ - f₂ 1| ≤ (L : ℝ) / 12 := by
  have hc := hL.continuousOn
  have hi₁ : IntervalIntegrable (fun t : ℝ => t * f₃ t) volume 0 1 :=
    (continuous_id.continuousOn.mul hc).intervalIntegrable_of_Icc (by norm_num : (0 : ℝ) ≤ 1)
  have hi₂ : IntervalIntegrable (fun t : ℝ => t * (1 - t) * f₃ t) volume 0 1 :=
    (((by fun_prop : Continuous (fun t : ℝ => t * (1 - t))).continuousOn).mul hc).intervalIntegrable_of_Icc
      (by norm_num : (0 : ℝ) ≤ 1)
  have haux : (∫ t in (0 : ℝ)..1, t * f₃ t) = f₂ 1 - f₁ 1 + f₁ 0 := by
    have hd (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
        HasDerivAt (fun t : ℝ => t * f₂ t - f₁ t) (t * f₃ t) t := by
      convert! ((hasDerivAt_id t).mul (h₃ t ht)).sub (h₂ t ht) using 1
      simp only [id_eq]
      ring
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t ht => hd t (by simpa using ht)) hi₁
    simpa only [one_mul, zero_mul, zero_sub, sub_neg_eq_add] using h
  have hvalue : f₁ 1 - f₁ 0 - 6 * trapezoidDefect f f₁ - f₂ 1 =
      ∫ t in (0 : ℝ)..1, (2 * t - 3 * t ^ 2) * f₃ t := by
    have he : (fun t : ℝ => (2 * t - 3 * t ^ 2) * f₃ t) =
        (fun t : ℝ => 3 * (t * (1 - t) * f₃ t) - t * f₃ t) := by ext t; ring
    rw [he, intervalIntegral.integral_sub (hi₂.const_mul 3) hi₁,
      intervalIntegral.integral_const_mul, haux,
      trapezoid_integral f f₁ f₂ f₃ h₁ h₂ h₃ hc]
    ring
  let p := fun t : ℝ => t ^ 2 * (1 - t)
  have hp : AbsolutelyContinuousOnInterval p 0 1 :=
    (by fun_prop : ContDiff ℝ 1 p).contDiffOn.absolutelyContinuousOnInterval
  have hLa : AbsolutelyContinuousOnInterval f₃ 0 1 :=
    (by simpa using hL : LipschitzOnWith L f₃ (uIcc 0 1)).absolutelyContinuousOnInterval
  have hibp := hp.integral_mul_deriv_eq_deriv_mul hLa
  have hdp : ∀ t, deriv p t = 2 * t - 3 * t ^ 2 := fun t => (endpoint_kernel_hasDerivAt t).deriv
  simp only [hdp, p, one_pow, sub_self, mul_zero, zero_pow (by decide : 2 ≠ 0),
    zero_mul, sub_zero, zero_sub] at hibp
  have he : f₁ 1 - f₁ 0 - 6 * trapezoidDefect f f₁ - f₂ 1 =
      -(∫ t in (0 : ℝ)..1, t ^ 2 * (1 - t) * deriv f₃ t) := by
    rw [hvalue]
    linarith only [hibp]
  have hb := intervalIntegral.norm_integral_le_of_norm_le (μ := volume)
    (by norm_num : (0 : ℝ) ≤ 1)
    (f := fun t : ℝ => t ^ 2 * (1 - t) * deriv f₃ t)
    (g := fun t : ℝ => (L : ℝ) * (t ^ 2 * (1 - t)))
    (by
      filter_upwards [volume.ae_ne (1 : ℝ)] with t ht hmem
      have ht₁ : t < 1 := lt_of_le_of_ne hmem.2 ht
      have hnorm := norm_deriv_le_of_lipschitzOn (Icc_mem_nhds hmem.1 ht₁) hL
      have hn : 0 ≤ t ^ 2 * (1 - t) := mul_nonneg (sq_nonneg _) (sub_nonneg.mpr hmem.2)
      rw [norm_mul, Real.norm_eq_abs (t ^ 2 * (1 - t)), abs_of_nonneg hn]
      exact (mul_le_mul_of_nonneg_left hnorm hn).trans_eq (mul_comm _ _))
    ((by fun_prop : Continuous _).intervalIntegrable 0 1)
  rw [intervalIntegral.integral_const_mul, integral_endpoint_kernel, Real.norm_eq_abs] at hb
  rw [he, abs_neg]
  nlinarith only [hb]

end
end krylov.Functions
