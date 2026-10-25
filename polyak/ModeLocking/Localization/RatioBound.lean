import polyak.ModeLocking.Localization.Defect

/-! A uniform endpoint-safe lower bound on every bounded shift interval. -/
noncomputable section
namespace polyak.ModeLocking.Localization
open Levels Set

theorem sineRatio_ge_half (q : General.Tuning) (s t : ℝ) (ω : Frequency)
    (hst : |s-t| ≤ 1) : (1/2:ℝ) ≤ sineRatio q s t ω := by
  let u := Geometry.shiftNumerator q t ω
  let v := Real.sin (ω:ℝ)
  let r := Geometry.shiftRadius q t ω
  let R := Geometry.shiftRadius q s ω
  have hr : 0 < r := Geometry.shiftRadius_pos q t ω.property
  have hR : 0 < R := Geometry.shiftRadius_pos q s ω.property
  have hr2 : r^2 = u^2+v^2 := Real.sq_sqrt (by positivity)
  have he : Geometry.shiftNumerator q s ω = u+(s-t)*v := by
    dsimp [u, v, Geometry.shiftNumerator]
    ring
  have hR2 : R^2 = (u+(s-t)*v)^2+v^2 := by
    dsimp [R,Geometry.shiftRadius]
    rw [Real.sq_sqrt (by positivity), he]
  have hds : (s-t)^2 ≤ 1 := by nlinarith [sq_abs (s-t), abs_nonneg (s-t)]
  have hmul : ((s-t)*v)^2 ≤ v^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hds) (sq_nonneg v)]
  have hbound : R ≤ 2*r := by
    nlinarith [sq_nonneg (u-(s-t)*v), sq_nonneg u, sq_nonneg v]
  change (1/2:ℝ) ≤ r/R
  apply (le_div_iff₀ hR).mpr
  linarith

end polyak.ModeLocking.Localization
