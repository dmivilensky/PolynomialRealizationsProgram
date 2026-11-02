import jacobi.Jacobi.StandardEnergyFormula

/-!
The exact mass of the one-sided standard Green diagonal.
Power integration covers every nonzero parameter; the logarithmic moment
handles zero directly. Use: the profile normalization agrees with the
actual finite resolvent trace and the Bessel spectral mass.
Article: jacobi, Section 5.5 and Theorem 5.6.
Article role: the exact one-sided diagonal mass used in the flow remainder.
-/
namespace jacobi.Jacobi
noncomputable section
open Real Set MeasureTheory jacobi.Analysis
set_option backward.isDefEq.respectTransparency false

/-- The genuine one-sided diagonal has precisely the prescribed mass,
including the logarithmic parameter. No trace-integral identity is assumed.
Article: jacobi, Section 5.5 and Theorem 5.6.
-/
theorem standard_diagonal_mass {a : ℝ} (ha : -(1/2:ℝ)<a) :
    (∫ t in (0:ℝ)..1,standardLimitKernel a t t)=1/(2*(a+1)) := by
  by_cases ha0 : a=0
  · subst a
    have he : (∫ t in (0:ℝ)..1,standardLimitKernel 0 t t)=
        -2*(∫ t in (0:ℝ)..1,t*log t) := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro t ht
      exact standard_diagonal_zero (by simpa only [min_eq_left (by norm_num : (0:ℝ)≤1)] using ht.1)
    have hm := logMoment_formula 0 1
    norm_num [logMoment] at hm
    rw [he,hm]
    norm_num
  · have he : (∫ t in (0:ℝ)..1,standardLimitKernel a t t)=
        ∫ t in (0:ℝ)..1,(t-t^(2*a+1))/a := by
      apply intervalIntegral.integral_congr_uIoo
      intro t ht
      exact standard_diagonal_formula ha0
        (by simpa only [min_eq_left (by norm_num : (0:ℝ)≤1)] using ht.1)
    have hI : IntervalIntegrable (fun t : ℝ => t^(2*a+1)) volume 0 1 :=
      intervalIntegral.intervalIntegrable_rpow' (by linarith)
    have hI0 : IntervalIntegrable (fun t : ℝ => t) volume 0 1 := continuous_id.intervalIntegrable 0 1
    rw [he,intervalIntegral.integral_div,
      intervalIntegral.integral_sub hI0 hI,
      integral_id,standard_unit_power_integral (by linarith : -1<2*a+1)]
    norm_num only [one_pow,zero_pow (by decide : (2:ℕ)≠0),sub_zero]
    field_simp (disch := first | assumption | positivity | linarith)
    ring

end
end jacobi.Jacobi
