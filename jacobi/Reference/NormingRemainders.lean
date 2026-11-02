import jacobi.Reference.NormingBounds
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
Article: jacobi, Appendix C.2 (norming ratios).
The actual logarithm and exponential have quantitative quadratic
remainders. These community Taylor estimates control the passage
from the original norming product to its first-order correction.
Use: norming_log_linearization sums the actual logarithm errors of all original norming factors without introducing an asymptotic expansion as a premise.
-/
namespace jacobi.Reference
noncomputable section
open Real Finset

/-- The true real logarithm has a uniform quadratic error on the half-unit interval.
Use: norming_log_linearization sums the actual logarithm errors of all original norming factors without introducing an asymptotic expansion as a premise.
Article: jacobi, Appendix C.2 (norming ratios).
Source: the real logarithm Taylor remainder, Real.abs_log_sub_add_sum_range_le.
Proof: specialize the proved Taylor bound at -x with one term, then use 1-abs(x)>=1/2 to bound its genuine remainder. -/
theorem log_one_add_quadratic {x : ℝ} (hx : |x|≤1/2) :
    |Real.log (1+x)-x|≤2*x^2 := by
  -- This is an estimate for the original principal real logarithm throughout the entire required small-factor range.
  have h := Real.abs_log_sub_add_sum_range_le (x := -x) (by simpa only [abs_neg] using (hx.trans_lt (by norm_num : (1/2:ℝ)<1))) 1
  norm_num only [Finset.sum_range_one,pow_one,Nat.cast_zero,zero_add,div_one,sub_neg_eq_add,abs_neg] at h
  have hp : 0<1-|x| := by linarith
  have hq : |x|^2/(1-|x|)≤2*x^2 := by
    apply (div_le_iff₀ hp).mpr
    rw [sq_abs]
    nlinarith [mul_nonneg (sq_nonneg x) (show 0≤1/2-|x| by linarith)]
  have hh : |Real.log (1+x)-x|≤|x|^2/(1-|x|) := by
    simpa only [sub_eq_add_neg,add_comm] using h
  exact hh.trans hq

/-- The true exponential has a global quadratic remainder controlled by the exponential of the absolute argument.
Use: normingRatio_asymptotic passes from the proved true log-rho expansion back to the actual positive norming ratio with an O(k^-4) extra error.
Article: jacobi, Appendix C.2 (norming ratios).
Source: Complex.norm_exp_sub_sum_le_norm_mul_exp, the proved exponential-series remainder.
Proof: specialize the community complex bound at the genuine real argument and degree two; its first two Taylor terms are exactly 1+x. -/
theorem exp_sub_one_sub_self_bound (x : ℝ) :
    |Real.exp x-1-x|≤x^2*Real.exp |x| := by
  have h := Complex.norm_exp_sub_sum_le_norm_mul_exp (x:ℂ) 2
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add,pow_zero,pow_one,
    Nat.factorial_zero,Nat.factorial_one,Nat.cast_one,div_one] at h
  simpa only [← Complex.ofReal_exp,← Complex.ofReal_one,← Complex.ofReal_add,
    ← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,sq_abs,sub_add_eq_sub_sub] using h

end
end jacobi.Reference
