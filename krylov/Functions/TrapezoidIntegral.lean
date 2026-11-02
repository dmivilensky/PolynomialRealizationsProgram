import krylov.Functions.HiddenCubic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
Article: main_krylov, thm:Fexact, the smooth trapezoid defect identity.
Use: derive a genuine integral formula from three actual derivatives, and
control its difference from the endpoint third derivative by the sharp 1/24.
Source: two integrations by parts in Appendix G; the proof below packages
them as one explicitly differentiated primitive and reuses mathlib's FTC.
-/

namespace krylov.Functions
noncomputable section
open Set MeasureTheory

/-- The normalized trapezoid defect from genuine values and endpoint derivatives.
Article: main_krylov, thm:Fexact. -/
def trapezoidDefect (f f₁ : ℝ → ℝ) : ℝ := f 1 - f 0 - (f₁ 0 + f₁ 1) / 2

/-- The exact integral of the cubic trapezoid weight.
Article: main_krylov, thm:Fexact. Proof: the explicit polynomial primitive. -/
theorem integral_trapezoid_weight :
    (∫ t in (0 : ℝ)..1, t * (1 - t)) = 1 / 6 := by
  have hd (t : ℝ) : HasDerivAt (fun t : ℝ => t ^ 2 / 2 - t ^ 3 / 3)
      (t * (1 - t)) t := by
    convert! (((hasDerivAt_id t).pow 2).div_const 2).sub
      (((hasDerivAt_id t).pow 3).div_const 3) using 1
    simp only [id_eq]
    ring
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t (_ : t ∈ uIcc (0 : ℝ) 1) => hd t)
    ((by fun_prop : Continuous (fun t : ℝ => t * (1 - t))).intervalIntegrable 0 1)
  norm_num at h ⊢
  exact h

/-- The exact integral governing the endpoint Lipschitz remainder.
Article: main_krylov, thm:Fexact. Proof: the explicit quartic primitive. -/
theorem integral_trapezoid_endpoint_weight :
    (∫ t in (0 : ℝ)..1, t * (1 - t) ^ 2) = 1 / 12 := by
  have hd (t : ℝ) : HasDerivAt
      (fun t : ℝ => t ^ 2 / 2 - 2 * t ^ 3 / 3 + t ^ 4 / 4) (t * (1 - t) ^ 2) t := by
    convert! ((((hasDerivAt_id t).pow 2).div_const 2).sub
      ((HasDerivAt.const_mul 2 ((hasDerivAt_id t).pow 3)).div_const 3)).add
      (((hasDerivAt_id t).pow 4).div_const 4) using 1
    simp only [id_eq]
    ring
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t (_ : t ∈ uIcc (0 : ℝ) 1) => hd t)
    ((by fun_prop : Continuous (fun t : ℝ => t * (1 - t) ^ 2)).intervalIntegrable 0 1)
  norm_num at h ⊢
  exact h

/-- Three genuine derivatives give the exact third-derivative trapezoid formula.
Article: main_krylov, thm:Fexact.
Proof: differentiate t(1-t)f''-(1-2t)f'-2f and apply the existing FTC. -/
theorem trapezoid_integral (f f₁ f₂ f₃ : ℝ → ℝ)
    (h₁ : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt f (f₁ t) t)
    (h₂ : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt f₁ (f₂ t) t)
    (h₃ : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt f₂ (f₃ t) t)
    (hc : ContinuousOn f₃ (Icc 0 1)) :
    trapezoidDefect f f₁ = -(1 / 2 : ℝ) * ∫ t in (0 : ℝ)..1, t * (1 - t) * f₃ t := by
  let P := fun t : ℝ => t * (1 - t) * f₂ t - (1 - 2 * t) * f₁ t - 2 * f t
  have hP (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivAt P (t * (1 - t) * f₃ t) t := by
    have hw := (hasDerivAt_id t).mul ((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t))
    have hw' := (hasDerivAt_const t (1 : ℝ)).sub (HasDerivAt.const_mul 2 (hasDerivAt_id t))
    convert! ((hw.mul (h₃ t ht)).sub (hw'.mul (h₂ t ht))).sub
      (HasDerivAt.const_mul 2 (h₁ t ht)) using 1
    simp only [Pi.mul_apply, Pi.sub_apply, id_eq]
    ring
  have hi : IntervalIntegrable (fun t : ℝ => t * (1 - t) * f₃ t) volume 0 1 :=
    ((continuous_id.continuousOn.mul
    (continuousOn_const.sub continuous_id.continuousOn)).mul hc).intervalIntegrable_of_Icc
    (by norm_num : (0 : ℝ) ≤ 1)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => hP t (by simpa using ht)) hi
  simp only [P, mul_zero, mul_one, one_mul, zero_mul, sub_zero] at h
  unfold trapezoidDefect
  linarith

/-- Lipschitz control of the third derivative gives the sharp endpoint defect bound.
Article: main_krylov, thm:Fexact, |delta_tr+T(1)/12| ≤ L/24 on the unit segment.
Proof: integrate the actual endpoint difference against the nonnegative kernel;
its exact remaining first moment is 1/12. -/
theorem trapezoid_endpoint_remainder (f f₁ f₂ f₃ : ℝ → ℝ)
    (h₁ : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt f (f₁ t) t)
    (h₂ : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt f₁ (f₂ t) t)
    (h₃ : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt f₂ (f₃ t) t)
    (hc : ContinuousOn f₃ (Icc 0 1)) (L : ℝ)
    (hL : ∀ t ∈ Icc (0 : ℝ) 1, |f₃ t - f₃ 1| ≤ L * (1 - t)) :
    |trapezoidDefect f f₁ + f₃ 1 / 12| ≤ L / 24 := by
  have hi : IntervalIntegrable (fun t : ℝ => t * (1 - t) * (f₃ t - f₃ 1)) volume 0 1 :=
    ((continuous_id.continuousOn.mul (continuousOn_const.sub continuous_id.continuousOn)).mul
      (hc.sub continuousOn_const)).intervalIntegrable_of_Icc (by norm_num : (0 : ℝ) ≤ 1)
  have he : trapezoidDefect f f₁ + f₃ 1 / 12 =
      -(1 / 2 : ℝ) * ∫ t in (0 : ℝ)..1, t * (1 - t) * (f₃ t - f₃ 1) := by
    rw [trapezoid_integral f f₁ f₂ f₃ h₁ h₂ h₃ hc]
    rw [show (fun t : ℝ => t * (1 - t) * (f₃ t - f₃ 1)) =
      (fun t : ℝ => t * (1 - t) * f₃ t - t * (1 - t) * f₃ 1) from
      funext (fun t => mul_sub _ _ _)]
    rw [intervalIntegral.integral_sub
      (f := fun t : ℝ => t * (1 - t) * f₃ t)
      (g := fun t : ℝ => t * (1 - t) * f₃ 1)
      (((continuous_id.continuousOn.mul
        (continuousOn_const.sub continuous_id.continuousOn)).mul hc).intervalIntegrable_of_Icc
        (by norm_num : (0 : ℝ) ≤ 1))
      ((by fun_prop : Continuous _).intervalIntegrable 0 1),
      intervalIntegral.integral_mul_const, integral_trapezoid_weight]
    ring
  have hb := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) (by norm_num : (0 : ℝ) ≤ 1)
    (f := fun t : ℝ => t * (1 - t) * (f₃ t - f₃ 1))
    (g := fun t : ℝ => L * (t * (1 - t) ^ 2))
    (Filter.Eventually.of_forall fun t ht => by
      have ht₀ : 0 ≤ t := ht.1.le
      have ht₁ : 0 ≤ 1 - t := sub_nonneg.mpr ht.2
      simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg ht₀, abs_of_nonneg ht₁]
      calc
        _ ≤ t * (1 - t) * (L * (1 - t)) :=
          mul_le_mul_of_nonneg_left (hL t ⟨ht₀, ht.2⟩) (mul_nonneg ht₀ ht₁)
        _ = _ := by ring)
    ((by fun_prop : Continuous _).intervalIntegrable 0 1)
  rw [intervalIntegral.integral_const_mul, integral_trapezoid_endpoint_weight,
    Real.norm_eq_abs] at hb
  rw [he, abs_mul]
  norm_num
  linarith

end
end krylov.Functions
