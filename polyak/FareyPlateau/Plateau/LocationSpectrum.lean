import polyak.FareyPlateau.Plateau.LocationSource
import Mathlib.Analysis.Complex.Trigonometric

/-! The limiting undamped characteristic polynomial has exactly the two
unit-circle roots printed in proposition location. -/
noncomputable section
namespace polyak.FareyPlateau

theorem undamped_factorization (ω : ℝ) (z : ℂ) :
    z^2-(2*(Real.cos ω:ℂ))*z+1 =
      (z-Complex.exp ((ω:ℂ)*Complex.I))*(z-Complex.exp ((-ω:ℝ)*Complex.I)) := by
  rw [Complex.exp_ofReal_mul_I,Complex.exp_ofReal_mul_I,
    Real.cos_neg,Real.sin_neg]
  simp only [Complex.ofReal_neg]
  have hs : ((Real.sin ω:ℂ)^2+(Real.cos ω:ℂ)^2)=1 := by
    exact_mod_cast Real.sin_sq_add_cos_sq ω
  linear_combination -hs+(Real.sin ω:ℂ)^2*(Complex.I_sq)

theorem undamped_roots (ω : ℝ) (z : ℂ) :
    z^2-(2*(Real.cos ω:ℂ))*z+1=0 ↔
      z=Complex.exp ((ω:ℂ)*Complex.I) ∨ z=Complex.exp ((-ω:ℝ)*Complex.I) := by
  rw [undamped_factorization,mul_eq_zero,sub_eq_zero,sub_eq_zero]

end polyak.FareyPlateau
