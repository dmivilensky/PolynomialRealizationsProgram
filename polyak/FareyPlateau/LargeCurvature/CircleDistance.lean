import polyak.FareyPlateau.LargeCurvature.ThreeLag
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! Quantitative distance to the complete integer lattice of turns. -/
noncomputable section
namespace polyak.FareyPlateau.LargeCurvature
open Real

def turnIndex (x : ℝ) : ℤ := round (x / (2 * Real.pi))
def turnDistance (x : ℝ) : ℝ := |x - (turnIndex x : ℝ) * (2 * Real.pi)|

theorem turnDistance_nonneg (x : ℝ) : 0 ≤ turnDistance x := abs_nonneg _

theorem turnDistance_le (x : ℝ) (z : ℤ) : turnDistance x ≤ |x - (z : ℝ) * (2 * Real.pi)| := by
  have hh := mul_le_mul_of_nonneg_left (round_le (x / (2 * Real.pi)) z)
    (show 0 ≤ 2 * Real.pi by positivity)
  have he (m : ℤ) : 2 * Real.pi * |x / (2 * Real.pi) - (m : ℝ)| =
      |x - (m : ℝ) * (2 * Real.pi)| := by
    calc
      _ = |(2 * Real.pi) * (x / (2 * Real.pi) - (m : ℝ))| := by
        rw [abs_mul, abs_of_pos (show 0 < 2 * Real.pi by positivity)]
      _ = _ := by congr 1; field_simp
  rw [he, he] at hh
  exact hh

theorem turnDistance_le_pi (x : ℝ) : turnDistance x ≤ Real.pi := by
  have hh := mul_le_mul_of_nonneg_left (abs_sub_round (x / (2 * Real.pi)))
    (show 0 ≤ 2 * Real.pi by positivity)
  have he : 2 * Real.pi * |x / (2 * Real.pi) - (round (x / (2 * Real.pi)) : ℝ)| =
      turnDistance x := by
    calc
      _ = |(2 * Real.pi) * (x / (2 * Real.pi) - (round (x / (2 * Real.pi)) : ℝ))| := by
        rw [abs_mul, abs_of_pos (show 0 < 2 * Real.pi by positivity)]
      _ = _ := by unfold turnDistance turnIndex; congr 1; field_simp
  rw [he] at hh
  linarith

theorem cos_turnDistance (x : ℝ) : Real.cos (turnDistance x) = Real.cos x := by
  rw [turnDistance, Real.cos_abs, Real.cos_sub_int_mul_two_pi]

theorem turnDistance_sub_le (x y : ℝ) : turnDistance (x - y) ≤ turnDistance x + turnDistance y := by
  have hh := turnDistance_le (x - y) (turnIndex x - turnIndex y)
  have he : (x - y) - ((turnIndex x - turnIndex y : ℤ) : ℝ) * (2 * Real.pi) =
      (x - (turnIndex x : ℝ) * (2 * Real.pi)) -
        (y - (turnIndex y : ℝ) * (2 * Real.pi)) := by push_cast; ring
  rw [he] at hh
  exact hh.trans (abs_sub _ _)

theorem turnDistance_lipschitz (x y : ℝ) : turnDistance x ≤ turnDistance y + |x - y| := by
  have hh := turnDistance_le x (turnIndex y)
  have he : x - (turnIndex y : ℝ) * (2 * Real.pi) =
      (y - (turnIndex y : ℝ) * (2 * Real.pi)) + (x - y) := by ring
  rw [he] at hh
  exact hh.trans (abs_add_le _ _)

theorem one_sub_cos_quadratic {x : ℝ} (hx : |x| ≤ Real.pi) :
    2 * x^2 / Real.pi^2 ≤ 1 - Real.cos x := by
  have hy := Real.mul_le_sin (show 0 ≤ |x| / 2 by positivity)
    (show |x| / 2 ≤ Real.pi / 2 by linarith)
  have hsin : 0 ≤ Real.sin (|x| / 2) := Real.sin_nonneg_of_nonneg_of_le_pi
    (by positivity) (by linarith [Real.pi_pos])
  have hsq := (sq_le_sq₀ (show 0 ≤ (2 / Real.pi) * (|x| / 2) by positivity) hsin).mpr hy
  have hid := Real.cos_two_mul (|x| / 2)
  rw [show 2 * (|x| / 2) = |x| by ring, Real.cos_abs] at hid
  have htrig := Real.sin_sq_add_cos_sq (|x| / 2)
  have he : ((2 / Real.pi) * (|x| / 2))^2 = x^2 / Real.pi^2 := by
    field_simp
    rw [sq_abs]
  rw [he] at hsq
  rw [show 2 * x^2 / Real.pi^2 = 2 * (x^2 / Real.pi^2) by ring]
  linarith

theorem one_sub_cos_distance (x : ℝ) :
    2 * (turnDistance x)^2 / Real.pi^2 ≤ 1 - Real.cos x := by
  have hh := one_sub_cos_quadratic (x := turnDistance x)
    (by rw [abs_of_nonneg (turnDistance_nonneg x)]; exact turnDistance_le_pi x)
  rwa [cos_turnDistance] at hh

theorem rational_turnDistance_lower {k n : ℤ} (hk : 0 < k) (hndvd : ¬k ∣ n) :
    2 * Real.pi / k ≤ turnDistance (2 * Real.pi * n / k) := by
  let z := turnIndex (2 * Real.pi * n / k)
  have hne : n - z * k ≠ 0 := by
    intro he
    apply hndvd
    exact ⟨z, by nlinarith⟩
  have hi : (1 : ℝ) ≤ |((n - z * k : ℤ) : ℝ)| := by
    have hh : 1 ≤ (n - z * k).natAbs := Int.natAbs_pos.mpr hne
    have hr : (1 : ℝ) ≤ ((n - z * k).natAbs : ℝ) := by exact_mod_cast hh
    simpa only [Nat.cast_natAbs, Int.cast_abs] using hr
  have hkp : 0 < (k : ℝ) := by exact_mod_cast hk
  have he : 2 * Real.pi * (n : ℝ) / k - (z : ℝ) * (2 * Real.pi) =
      (2 * Real.pi / k) * ((n - z * k : ℤ) : ℝ) := by
    push_cast
    field_simp
  unfold turnDistance
  change _ ≤ |2 * Real.pi * (n : ℝ) / k - (z : ℝ) * (2 * Real.pi)|
  rw [he, abs_mul, abs_of_pos (div_pos (by positivity) hkp)]
  exact le_mul_of_one_le_right (by positivity) hi

end polyak.FareyPlateau.LargeCurvature
