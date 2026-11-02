import krylov.Asymptotics.StepAverages
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
Article: main_krylov, apC:lem:step, exact exponential averages.
Use: the printed E-plus/E-minus functions with their removable value one
at zero, continuity and elementary positive-axis bounds.
Source: the derivative of exp at zero and the elementary exponential tangent bound.
-/

namespace krylov.Asymptotics.ExactAverages
noncomputable section
open Real Set Filter
open scoped Topology

private def expDividedDifference (x : ℝ) : ℝ :=
  Function.update (fun y ↦ (exp y - 1) / y) 0 1 x

private theorem expDividedDifference_pos (x : ℝ) : 0 < expDividedDifference x := by
  by_cases hx : x = 0
  · subst x
    simp [expDividedDifference]
  · rw [expDividedDifference, Function.update_of_ne hx]
    rcases lt_or_gt_of_ne hx with hx | hx
    · exact div_pos_of_neg_of_neg (sub_neg.mpr (exp_lt_one_iff.mpr hx)) hx
    · exact div_pos (sub_pos.mpr (one_lt_exp_iff.mpr hx)) hx

private theorem expDividedDifference_continuous : Continuous expDividedDifference := by
  apply continuous_iff_continuousAt.mpr
  intro x
  by_cases hx : x = 0
  · subst x
    change ContinuousAt (Function.update (fun y ↦ (exp y - 1) / y) 0 1) 0
    simpa only [exp_zero, sub_zero] using
      (hasDerivAt_exp (0 : ℝ)).continuousAt_div
  · have hb : ContinuousAt (fun y : ℝ ↦ (exp y - 1) / y) x :=
      (continuous_exp.continuousAt.sub continuousAt_const).div continuousAt_id hx
    apply hb.congr_of_eventuallyEq
    filter_upwards [eventually_ne_nhds hx] with y hy
    exact Function.update_of_ne hy _ _

/-- The printed E-minus function x/(exp(x)-1), with its removable value
one at the origin. -/
def Eminus (x : ℝ) : ℝ := (expDividedDifference x)⁻¹

/-- The printed E-plus function x/(1-exp(-x)), with its removable value
one at the origin. -/
def Eplus (x : ℝ) : ℝ := exp x * Eminus x

/-- E-minus has removable value one at zero. -/
@[simp] theorem Eminus_zero : Eminus 0 = 1 := by simp [Eminus, expDividedDifference]

/-- E-plus has removable value one at zero. -/
@[simp] theorem Eplus_zero : Eplus 0 = 1 := by simp [Eplus]

/-- Away from zero E-minus equals its printed quotient. -/
theorem Eminus_eq {x : ℝ} (hx : x ≠ 0) : Eminus x = x / (exp x - 1) := by
  simp only [Eminus, expDividedDifference, Function.update_of_ne hx, inv_div]

/-- Away from zero E-plus equals its printed quotient. -/
theorem Eplus_eq {x : ℝ} (hx : x ≠ 0) : Eplus x = x / (1 - exp (-x)) := by
  rw [Eplus, Eminus_eq hx, exp_neg]
  have he : exp x - 1 ≠ 0 := sub_ne_zero.mpr (fun he ↦ hx (exp_injective (he.trans exp_zero.symm)))
  field_simp [he]

/-- Both exact-average factors are strictly positive on the whole real axis. -/
theorem Eminus_pos (x : ℝ) : 0 < Eminus x := inv_pos.mpr (expDividedDifference_pos x)

/-- E-plus is strictly positive on the whole real axis. -/
theorem Eplus_pos (x : ℝ) : 0 < Eplus x := mul_pos (exp_pos x) (Eminus_pos x)

/-- The removable definition makes E-minus continuous at zero as well as
on the nonzero axis. -/
theorem Eminus_continuous : Continuous Eminus :=
  expDividedDifference_continuous.inv₀ (fun x ↦ (expDividedDifference_pos x).ne')

/-- E-plus is continuous, including its removable origin value. -/
theorem Eplus_continuous : Continuous Eplus := continuous_exp.mul Eminus_continuous

/-- The exact identity used to multiply drift and impulse averages. -/
theorem exp_mul_Eminus (x : ℝ) : exp x * Eminus x = Eplus x := rfl

/-- E-plus is at least one on the nonnegative axis. -/
theorem one_le_Eplus {x : ℝ} (hx : 0 ≤ x) : 1 ≤ Eplus x := by
  rcases eq_or_lt_of_le hx with h0 | hp
  · rw [← h0, Eplus_zero]
  · rw [Eplus_eq hp.ne']
    have hd : 0 < 1 - exp (-x) := sub_pos.mpr (exp_lt_one_iff.mpr (neg_neg_of_pos hp))
    apply (le_div_iff₀ hd).mpr
    have hh := add_one_le_exp (-x)
    linarith

/-- E-minus is bounded below by exp(-x) on the nonnegative axis. -/
theorem exp_neg_le_Eminus {x : ℝ} (hx : 0 ≤ x) : exp (-x) ≤ Eminus x := by
  have hh := mul_le_mul_of_nonneg_left (one_le_Eplus hx) (exp_pos (-x)).le
  simpa only [Eplus, ← mul_assoc, ← exp_add, neg_add_cancel, exp_zero, one_mul,
    mul_one] using hh

end
end krylov.Asymptotics.ExactAverages
