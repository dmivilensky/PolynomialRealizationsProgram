import polyak.ModeLocking.Localization.Shift

/-! The shift derivative of the actual finite lag symbol. -/
noncomputable section
namespace polyak.ModeLocking.Localization
open Levels Set
open scoped BigOperators
variable {I : Type*} [Fintype I]

theorem hasDerivAt_phase_shift (q : General.Tuning) (s : ℝ) (ω : Frequency)
    (hω : ω ∈ Threshold.interiorCarrier) :
    HasDerivAt (fun u => Geometry.shiftedCurve q u ω)
      (-(Real.sin (Geometry.shiftedCurve q s ω))^2) s := by
  have hf : (fun u => Geometry.shiftedCurve q u ω) =
      (fun u => Geometry.arccotangent (Geometry.cotangent q ω + u)) := by
    funext u
    exact Geometry.shiftedAngle_eq_arccotangent q u hω
  rw [hf]
  have hh := (Geometry.hasDerivAt_arccotangent (Geometry.cotangent q ω+s)).comp s
    ((hasDerivAt_id s).const_add (Geometry.cotangent q ω))
  have hs := phase_sin_pos q s ω hω
  have hc := Geometry.cot_shiftedAngle q s hω
  have hid := Real.sin_sq_add_cos_sq (Geometry.shiftedCurve q s ω)
  have he : (Real.sin (Geometry.shiftedCurve q s ω))^2 *
      (1+(Geometry.cotangent q ω+s)^2)=1 := by
    change Real.cos (Geometry.shiftedCurve q s ω)/Real.sin (Geometry.shiftedCurve q s ω)=_ at hc
    change Real.cos (Geometry.shiftedCurve q s ω) / Real.sin (Geometry.shiftedCurve q s ω) =
      Geometry.cotangent q ω+s at hc
    have hcos := (div_eq_iff hs.ne').mp hc
    rw [hcos] at hid
    nlinarith only [hid]
  convert hh using 1
  · simp only [Function.comp_def]
  · simp only [mul_one]
    apply neg_inj.mpr
    exact (eq_div_iff (by positivity : (1+(Geometry.cotangent q ω+s)^2) ≠ 0)).mpr he

theorem hasDerivAt_symbol_quotient (q : General.Tuning) (s : ℝ) (n : I → ℤ)
    (a : I → ℝ) (γ : ℝ) (ω : Frequency) (hω : ω ∈ Threshold.interiorCarrier) :
    HasDerivAt (fun u => symbol q u n a γ ω / Real.sin (Geometry.shiftedCurve q u ω))
      (oscillation n a ω+γ) s := by
  have hf : (fun u => symbol q u n a γ ω / Real.sin (Geometry.shiftedCurve q u ω)) =
      (fun u => symbol q s n a γ ω / Real.sin (Geometry.shiftedCurve q s ω) +
        (u-s)*(oscillation n a ω+γ)) := by
    funext u
    exact shift_identity q u s n a γ ω hω
  rw [hf]
  convert (((hasDerivAt_id s).sub_const s).mul_const (oscillation n a ω+γ)).const_add
    (symbol q s n a γ ω / Real.sin (Geometry.shiftedCurve q s ω)) using 1
  · funext u
    rfl
  · ring

theorem hasDerivAt_symbol_shift (q : General.Tuning) (s : ℝ) (n : I → ℤ)
    (a : I → ℝ) (γ : ℝ) (ω : Frequency) (hω : ω ∈ Threshold.interiorCarrier) :
    HasDerivAt (fun u => symbol q u n a γ ω)
      ((Real.cos (Geometry.shiftedCurve q s ω) * (-(Real.sin (Geometry.shiftedCurve q s ω))^2)) /
        Real.sin (Geometry.shiftedCurve q s ω) * symbol q s n a γ ω +
        Real.sin (Geometry.shiftedCurve q s ω) * (oscillation n a ω+γ)) s := by
  have hs := (hasDerivAt_phase_shift q s ω hω).sin
  have hquot := hasDerivAt_symbol_quotient q s n a γ ω hω
  have he : (fun u => symbol q u n a γ ω) =
      (fun u => Real.sin (Geometry.shiftedCurve q u ω) *
        (symbol q u n a γ ω / Real.sin (Geometry.shiftedCurve q u ω))) := by
    funext u
    exact (mul_div_cancel₀ _ (phase_sin_pos q u ω hω).ne').symm
  rw [he]
  convert hs.mul hquot using 1
  ring

end polyak.ModeLocking.Localization
