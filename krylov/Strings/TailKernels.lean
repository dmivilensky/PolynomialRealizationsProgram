import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
Article: main_krylov, apC:prop:tauber, the Stieltjes Tauberian bridge.
Use: compactify the positive spectral axis by u=t/(t+xi). The transformed
Stieltjes test functions are the continuous kernels (1+(a-1)u)^(-1).
Source: the resolvent-algebra proof of the Stieltjes continuity theorem,
using mathlib's real Stone-Weierstrass theorem rather than a Tauberian axiom.
-/

namespace krylov.Strings.Tail
noncomputable section
open Set Filter
open scoped Topology

/-- The compact space used for the scaled spectral measures. -/
abbrev UnitInterval := Icc (0 : ℝ) 1

/-- Positive relative Stieltjes parameters. -/
abbrev PositiveParameter := Ioi (0 : ℝ)

/-- Uniform positivity of the compactified Stieltjes denominator. -/
theorem kernel_denominator_lower (a : PositiveParameter) (u : UnitInterval) :
    min 1 (a : ℝ) ≤ 1 + ((a : ℝ) - 1) * (u : ℝ) := by
  rcases le_total (a : ℝ) 1 with ha | ha
  · rw [min_eq_right ha]
    nlinarith [mul_nonneg (sub_nonneg.mpr u.property.2) (sub_nonneg.mpr ha)]
  · rw [min_eq_left ha]
    exact le_add_of_nonneg_right (mul_nonneg (sub_nonneg.mpr ha) u.property.1)

/-- The compactified Stieltjes denominator is strictly positive. -/
theorem kernel_denominator_pos (a : PositiveParameter) (u : UnitInterval) :
    0 < 1 + ((a : ℝ) - 1) * (u : ℝ) :=
  (lt_min (by norm_num) a.property).trans_le (kernel_denominator_lower a u)

/-- Continuous Stieltjes kernel on the compactified spectral axis. -/
def kernel (a : PositiveParameter) : C(UnitInterval, ℝ) :=
  ⟨fun u ↦ 1 / (1 + ((a : ℝ) - 1) * (u : ℝ)),
    continuous_const.div (by fun_prop) (fun u ↦ (kernel_denominator_pos a u).ne')⟩

/-- Relative parameter one gives the constant test function. -/
@[simp] theorem kernel_one : kernel ⟨1, by norm_num⟩ = 1 := by
  ext u
  simp only [kernel, ContinuousMap.coe_mk, sub_self, zero_mul, add_zero, div_one,
    ContinuousMap.one_apply]

/-- The kernels depend continuously on their positive parameter in uniform norm. -/
theorem kernel_continuous : Continuous kernel := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun p : PositiveParameter × UnitInterval ↦
    1 / (1 + ((p.1 : ℝ) - 1) * (p.2 : ℝ)))
  exact continuous_const.div (by fun_prop) (fun p ↦ (kernel_denominator_pos p.1 p.2).ne')

/-- Distinct kernels have their product in their two-dimensional linear span. -/
theorem kernel_mul_of_ne (a b : PositiveParameter) (hab : a ≠ b) :
    kernel a * kernel b =
      (((a : ℝ) - 1) / ((a : ℝ) - b)) • kernel a +
        ((1 - (b : ℝ)) / ((a : ℝ) - b)) • kernel b := by
  have hab' : (a : ℝ) - b ≠ 0 := sub_ne_zero.mpr (fun h ↦ hab (Subtype.ext h))
  ext u
  change 1 / (1 + ((a : ℝ) - 1) * (u : ℝ)) *
      (1 / (1 + ((b : ℝ) - 1) * (u : ℝ))) = _
  simp only [ContinuousMap.add_apply, ContinuousMap.smul_apply, smul_eq_mul, kernel,
    ContinuousMap.coe_mk]
  have hbn : 1 + (b : ℝ) * (u : ℝ) - (u : ℝ) ≠ 0 := by
    nlinarith [kernel_denominator_pos b u]
  have hcancel := mul_inv_cancel₀ hbn
  field_simp [hab', (kernel_denominator_pos a u).ne', hbn]
  linear_combination ((a : ℝ) - 1) * hcancel

/-- One fixed nonconstant kernel already separates all compactified spectral points. -/
theorem kernel_two_injective : Function.Injective (kernel ⟨2, by norm_num⟩) := by
  intro u v huv
  change 1 / (1 + ((2 : ℝ) - 1) * (u : ℝ)) =
    1 / (1 + ((2 : ℝ) - 1) * (v : ℝ)) at huv
  have hh := congrArg (fun x : ℝ ↦ x⁻¹) huv
  simp only [one_div, inv_inv] at hh
  apply Subtype.ext
  linarith

end
end krylov.Strings.Tail
