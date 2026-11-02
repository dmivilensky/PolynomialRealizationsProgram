import jacobi.Jacobi.StandardFactor
import jacobi.Jacobi.StandardAsymptotic

/-!
The actual standard Jacobi coefficients and conductances at large degree.
Only elementary affine ratios and the proved genuine norm power law are
used. Together they give the inverse conductance scale for the Green tails.
Use: StandardJacobi passes the exact finite Green formula to its limit.
Article: jacobi, Theorem 5.4, Equation (5.10).
Article role: the endpoint and recurrence-coefficient power limits.
-/
namespace jacobi.Jacobi
noncomputable section
open Real Filter jacobi.Reference
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- An elementary affine natural-degree ratio with denominator slope two.
Article: jacobi, Theorem 5.4, Equation (5.10).
-/
theorem standard_half_ratio_limit (s t : ℝ) :
    Tendsto (fun n : ℕ => ((n:ℝ)+s)/(2*(n:ℝ)+t)) atTop (𝓝 (1/2:ℝ)) := by
  have h := (shifted_nat_ratio s (t/2)).div_const 2
  convert h using 1
  funext n
  rw [div_div]
  congr 1
  ring

/-- The true forward recurrence coefficient tends to one half.
Article: jacobi, Theorem 5.4, Equation (5.10).
-/
theorem standardForward_limit (a b : ℝ) :
    Tendsto (standardForward a b) atTop (𝓝 (1/2:ℝ)) := by
  have h := ((standard_half_ratio_limit (a+1) (a+b+1)).mul
    (standard_half_ratio_limit (a+b+1) (a+b+2))).const_mul 2
  norm_num only [mul_one_div,mul_div_assoc] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0:ℕ)] with n hn
  rw [standardForward,ite_eq_right (Nat.ne_of_gt hn)]
  simp only [div_eq_mul_inv,mul_inv_rev,add_assoc]
  ring

/-- The true backward recurrence coefficient tends to one half.
Article: jacobi, Theorem 5.4, Equation (5.10).
-/
theorem standardBackward_limit (a b : ℝ) :
    Tendsto (standardBackward a b) atTop (𝓝 (1/2:ℝ)) := by
  have h := ((standard_half_ratio_limit 0 (a+b)).mul
    (standard_half_ratio_limit b (a+b+1))).const_mul 2
  norm_num only [mul_one_div,mul_div_assoc] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0:ℕ)] with n hn
  rw [standardBackward,ite_eq_right (Nat.ne_of_gt hn)]
  simp only [add_zero,div_eq_mul_inv,mul_inv_rev,add_assoc]
  ring

/-- The actual conductance has its full positive endpoint-square power
constant divided by two, independent of any matrix size truncation.
Article: jacobi, Theorem 5.4, Equation (5.10).
-/
theorem standardConductance_power_limit {a b : ℝ} (ha : -1<a) (hb : -1<b) :
    Tendsto (fun n : ℕ => standardConductance a b n/(n:ℝ)^(2*a+1)) atTop
      (𝓝 (standardEndpointConstant a b/2)) := by
  have h := (standardEndpointSquare_power_limit ha hb).mul (standardForward_limit a b)
  simp only [mul_one_div] at h
  convert h using 1
  funext n
  dsimp [standardConductance]
  ring

end
end jacobi.Jacobi
