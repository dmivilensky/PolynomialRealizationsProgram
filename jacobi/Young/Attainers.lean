import jacobi.Young.Calibration
import jacobi.Variational.Translation

/-!
Article: jacobi, Section 3.2 (sharp Young inequality).
Every nonnegative amplitude and every real center gives a literal density
attaining the exact sharp inequality. This proves the sufficient equality
direction and sharpness of the constant; necessity of this family is a
separate classification theorem and is not claimed here.
Use: proves sharpness of the constant and the sufficient equality direction.
-/
namespace jacobi.Young
noncomputable section
open MeasureTheory Real jacobi.Variational
set_option backward.isDefEq.respectTransparency false

/-- Every actual sech^4 profile attains the printed sharp Young inequality.
Use: proves sharpness of the constant and the sufficient equality direction.
Article: jacobi, Section 3.2 (sharp Young inequality).
Proof: the exact second moment and energy agree after cubing; all quantities
are nonnegative, so equality of cubes is equivalent to equality. -/
theorem equalityFamily_sharp {b : ℝ} (hb : 0 ≤ b) :
    observe (equalityFamily b hb) .second =
      (5/18 : ℝ)^(1/3 : ℝ)*(equalityFamily b hb).energy^(4/3 : ℝ) := by
  -- Work with rational polynomial identities until the final injective cube map.
  let m := equalityFamily b hb
  have hG0 : 0 ≤ observe m .second := tsum_nonneg (fun _ => sq_nonneg _)
  have hE0 : 0 ≤ m.energy := m.energy_nonneg
  have hc : ((5/18 : ℝ)^(1/3 : ℝ))^3=(5/18 : ℝ) := by
    simpa only [Nat.cast_one,pow_one] using third_power_cube (by norm_num : (0 : ℝ) ≤ 5/18) 1
  have hE : (m.energy^(4/3 : ℝ))^3=m.energy^4 := by
    simpa only [Nat.cast_ofNat] using third_power_cube m.energy_nonneg 4
  have hb6 : (b^(3/2 : ℝ))^4=b^6 := by
    rw [← rpow_natCast,← rpow_mul hb]
    norm_num
  have he : m.energy^4=(16/15 : ℝ)^4*b^6 := by
    rw [equalityFamily_energy,mul_pow,hb6]
  apply (pow_left_inj₀ hG0 (by positivity) (by decide : 3 ≠ 0)).mp
  rw [mul_pow,hc,hE,he]
  change (observe (equalityFamily b hb) .second)^3=(5/18 : ℝ)*((16/15 : ℝ)^4*b^6)
  rw [equalityFamily_second]
  ring

/-- Every translated literal profile attains the same exact sharp Young inequality.
Use: verifies all arbitrary centers in the printed sufficient equality statement.
Article: jacobi, Section 3.2 (sharp Young inequality).
Proof: translation preserves both the actual second spectral moment and the actual energy. -/
theorem translated_equalityFamily_sharp {b : ℝ} (hb : 0 ≤ b) (a : ℝ) :
    observe ((equalityFamily b hb).translate a) .second =
      (5/18 : ℝ)^(1/3 : ℝ)*((equalityFamily b hb).translate a).energy^(4/3 : ℝ) := by
  rw [Density.translate_second,Density.translate_energy]
  exact equalityFamily_sharp hb

end
end jacobi.Young
