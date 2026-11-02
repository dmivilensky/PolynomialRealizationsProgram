import krylov.OneGradient.TwoDimensionalComparison
import Mathlib.Analysis.SpecialFunctions.Pow.Real
set_option autoImplicit false
/-!
Article: main_krylov, thm:local(c), literal printed two-branch value.
Use: identify the proved attained scalar maximum with the original formula,
including the exact real exponent three halves in the first branch.
Source: exact nonnegative square-root scaling and standard real powers.
-/

namespace krylov.OneGradient
noncomputable section

/-- The genuine attained two-dimensional scalar value is exactly the
printed source formula on both budget branches, including their threshold.
Use: the actual scalar optimization and strict RFC comparison concern
precisely the article's V_2, rather than an unidentified stationary value.
Article: main_krylov, thm:local(c), displayed V_2.
Proof: factor the positive W and three in the actual stationary square
root. The real power three halves is its positive argument times its
square root; the genuine root-square identity cancels the physical scale. -/
theorem twoDimensionalValue_formula (W w : ℝ) (hW : 0< W) (hw : 0≤ w) :
    twoDimensionalValue W w=if w≤ W/2 then
      (2/(3*Real.sqrt 3))*Real.sqrt W*(W+w)^((3 : ℝ)/2)
    else W*Real.sqrt (w^2+W^2/4) := by
  unfold twoDimensionalValue
  split_ifs with hbudget
  · have hWp : 0< W+w := by linarith
    have hr : (W+w)^((3 : ℝ)/2)=(W+w)*Real.sqrt (W+w) := by
      rw [show (3 : ℝ)/2=1+1/2 by norm_num,Real.rpow_add hWp,Real.rpow_one,← Real.sqrt_eq_rpow]
    rw [hr,Real.sqrt_div hWp.le,Real.sqrt_mul (by norm_num : (0 : ℝ)≤3)]
    have hs := Real.sq_sqrt hW.le
    have hsW : Real.sqrt W≠0 := (Real.sqrt_pos.mpr hW).ne'
    have hs3 : Real.sqrt 3≠0 := (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ)<3)).ne'
    field_simp
    nlinarith
  · rfl

end
end krylov.OneGradient
