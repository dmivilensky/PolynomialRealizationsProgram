import polyak.Boundary.P5.System

/-!
Article: the four actual active constraints of the regularized P5 system.
Use: exact division, rather than a limiting condition, gives their zeros on a solution branch.
-/
noncomputable section
namespace polyak.Boundary.P5
open Spectral

/-- Article: the normalized lower constraint is precisely the signed source primal. -/
theorem actualPrimal_lower (h : ℝ) (Z : Coordinates) (n : ℕ) :
    actualPrimal h Z n (-1)=
      (1-h*Z 3)*normalizedLower (1/2+h*Z 0) (1+h) n (-1/2+h*Z 1)+
        h*Z 3*normalizedLower (1/2+h*Z 0) (1+h) n (Z 2)+h*Z 4 := by
  unfold actualPrimal actualRaw normalizedLower
  ring

/-- Article: the normalized upper constraint is precisely the signed source primal. -/
theorem actualPrimal_upper (h : ℝ) (Z : Coordinates) (n : ℕ) :
    actualPrimal h Z n 1=
      (1-h*Z 3)*normalizedUpper (1/2+h*Z 0) (1+h) n (-1/2+h*Z 1)+
        h*Z 3*normalizedUpper (1/2+h*Z 0) (1+h) n (Z 2)-h*Z 4 := by
  unfold actualPrimal actualRaw normalizedUpper
  ring

/-- Article: all four source active slacks vanish at every actual nonnegative-parameter solution. -/
theorem active_slacks_zero {h : ℝ} (hh : 0≤h) {Z : Coordinates}
    (hz : regularSystem (h,Z)=0) :
    actualPrimal h Z 1 (-1)=0 ∧ actualPrimal h Z 2 1=0 ∧
      actualPrimal h Z 3 1=0 ∧ actualPrimal h Z 5 1=0 := by
  obtain ⟨h1,h2,h3,h5⟩ := regularSystem_primal_exact hh Z
  rw [hz] at h1 h2 h3 h5
  norm_num only [Pi.zero_apply,mul_zero] at h1 h2 h3 h5
  have hd1 := (lagDenominator_pos (by linarith : (1 : ℝ)≤1+h) 1 (by omega)).ne'
  have hd2 := (lagDenominator_pos (by linarith : (1 : ℝ)≤1+h) 2 (by omega)).ne'
  have hd3 := (lagDenominator_pos (by linarith : (1 : ℝ)≤1+h) 3 (by omega)).ne'
  have hd5 := (lagDenominator_pos (by linarith : (1 : ℝ)≤1+h) 5 (by omega)).ne'
  exact ⟨(mul_eq_zero.mp h1.symm).resolve_left hd1,
    (mul_eq_zero.mp h2.symm).resolve_left (mul_ne_zero (by norm_num) hd2),
    (mul_eq_zero.mp h3.symm).resolve_left (mul_ne_zero (by norm_num) hd3),
    (mul_eq_zero.mp h5.symm).resolve_left (mul_ne_zero (by norm_num) hd5)⟩

end polyak.Boundary.P5
