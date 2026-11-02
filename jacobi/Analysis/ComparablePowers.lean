import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
Article: jacobi, Appendix C.3 (support weights and segment bounds).
Positive quantities within a factor two have uniformly comparable real
powers, including negative exponents. The support-weight estimate needs
this for the exponent 2*gamma_beta-1, which can have either sign.
Source: elementary monotonicity of positive real powers.
Use: supportWeight_ratio_bounds controls the reflected beta sine product on the entire right spectral half, including gamma_beta<1/2.
-/
namespace jacobi.Analysis
noncomputable section
open Real

/-- Powers of two positive quantities within a factor two are uniformly comparable for every real exponent.
Use: supportWeight_ratio_bounds controls the reflected beta sine product on the entire right spectral half, including gamma_beta<1/2.
Article: jacobi, Appendix C.3 (support weights and segment bounds).
Proof: divide the two original bases. Their ratio lies in [1/2,1]; compare its exponent with plus and minus the absolute exponent, then compare the base with 1/2. Multiply back by the genuine positive denominator power. -/
theorem comparable_powers {x y:ℝ} (hy:0<y) (hlo:y/2≤x) (hhi:x≤y) (e:ℝ) :
    (1/2:ℝ)^|e| *y^e≤x^e ∧ x^e≤(1/2:ℝ)^(-|e|)*y^e := by
  -- This argument avoids splitting the actual endpoint exponent into separate cases.
  have hx : 0<x := lt_of_lt_of_le (by positivity : 0<y/2) hlo
  have hr0 : 0<x/y := div_pos hx hy
  have hrlo : (1/2:ℝ)≤x/y := (le_div_iff₀ hy).mpr (by linarith)
  have hrhi : x/y≤1 := (div_le_one hy).mpr hhi
  have hl : (1/2:ℝ)^|e|≤(x/y)^e :=
    (rpow_le_rpow (by norm_num) hrlo (abs_nonneg e)).trans
      (rpow_le_rpow_of_exponent_ge hr0 hrhi (le_abs_self e))
  have hu : (x/y)^e≤(1/2:ℝ)^(-|e|) :=
    (rpow_le_rpow_of_exponent_ge hr0 hrhi (neg_abs_le e)).trans
      (rpow_le_rpow_of_nonpos (by norm_num) hrlo (neg_nonpos.mpr (abs_nonneg e)))
  rw [div_rpow hx.le hy.le] at hl hu
  exact ⟨(le_div_iff₀ (rpow_pos_of_pos hy e)).mp hl,
    (div_le_iff₀ (rpow_pos_of_pos hy e)).mp hu⟩

end
end jacobi.Analysis
