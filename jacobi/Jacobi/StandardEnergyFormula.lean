import jacobi.Jacobi.StandardEnergyLimit
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import jacobi.Analysis.LogMoments

/-!
Exact one-sided Jacobi diagonal and energy integrals.
The power formula is evaluated directly when a is nonzero. The logarithmic
case uses a continuous polynomial in t and t*log(t) as an explicit primitive,
so the singular endpoint contributes no assumed limiting boundary term.
Use: StandardJacobi obtains the printed initial energy constant of the
actual standard chain, including the logarithmic parameter zero.
Article: jacobi, Theorem 5.4.
Article role: dominated convergence and exact power or logarithmic evaluation of the one-sided
energy.
-/
namespace jacobi.Jacobi
noncomputable section
open Real Set Filter MeasureTheory
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The elementary unit-interval power integral, with its convergence
condition retained explicitly for every exponent used below.
Article: jacobi, Theorem 5.4.
-/
theorem standard_unit_power_integral {q : ℝ} (hq : -1<q) :
    (∫ t in (0:ℝ)..1,t^q)=1/(q+1) := by
  rw [integral_rpow (Or.inl hq)]
  simp only [one_rpow,zero_rpow (show q+1≠0 by linarith),sub_zero]

/-- The one-sided diagonal has its literal power-difference expression
at every positive point for each nonzero parameter.
Article: jacobi, Theorem 5.4.
-/
theorem standard_diagonal_formula {a t : ℝ} (ha : a≠0) (ht : 0<t) :
    standardLimitKernel a t t=(t-t^(2*a+1))/a := by
  have hp : 0<t^(2*a+1) := rpow_pos_of_pos ht _
  have hz : (0:ℝ)∉uIcc t 1 := by
    intro h
    exact (not_lt_of_ge h.1) (lt_min ht zero_lt_one)
  have hn : -(2*a+1)≠-1 := by intro h; apply ha; linarith
  have hi : (∫ v in t..1,1/v^(2*a+1))=
      (1-t^(-(2*a+1)+1))/(-(2*a+1)+1) := by
    have he : (∫ v in t..1,1/v^(2*a+1))=(∫ v in t..1,v^(-(2*a+1))) := by
      apply intervalIntegral.integral_congr
      intro v hv
      have hv0 : 0<v := (lt_min ht zero_lt_one).trans_le hv.1
      change 1/v^(2*a+1)=v^(-(2*a+1))
      rw [one_div,rpow_neg hv0.le]
    rw [he,integral_rpow (Or.inr ⟨hn,hz⟩),one_rpow]
  have hpow : t^(2*a+1)*t^(-(2*a+1)+1)=t := by
    rw [← rpow_add ht]
    rw [show 2*a+1+(-(2*a+1)+1)=(1:ℝ) by ring,rpow_one]
  rw [standardLimitKernel,max_self,sqrt_mul_self hp.le,hi]
  field_simp [ha,show -(2*a+1)+1≠0 by intro h; apply ha; linarith]
  linear_combination -2*a*hpow

/-- At the logarithmic parameter the diagonal is exactly -2*t*log(t).
The value zero at t=0 follows from its genuine endpoint prefactor.
Article: jacobi, Theorem 5.4.
-/
theorem standard_diagonal_zero {t : ℝ} (ht : 0≤t) :
    standardLimitKernel 0 t t= -2*(t*log t) := by
  by_cases ht0 : t=0
  · subst t
    simp [standardLimitKernel]
  · have htpos : 0<t := lt_of_le_of_ne ht (Ne.symm ht0)
    simp only [standardLimitKernel,mul_zero,zero_add,rpow_one,max_self,sqrt_mul_self ht]
    rw [integral_one_div_of_pos htpos zero_lt_one,one_div,log_inv]
    ring

/-- The logarithmic energy primitive is continuous even at zero,
because every occurrence of log is paired with its vanishing factor t.
Article: jacobi, Theorem 5.4.
-/
theorem standard_log_square_integral :
    (∫ t in (0:ℝ)..1,(t*log t)^2)=2/27 := by
  have h := jacobi.Analysis.logMoment_formula 0 2
  norm_num [jacobi.Analysis.logMoment] at h
  exact h

/-- The squared diagonal is a sum of three integrable powers whenever
a is nonzero. The formula includes the true zero endpoint.
Article: jacobi, Theorem 5.4.
-/
theorem standard_diagonal_square {a t : ℝ} (ha : -(1/2:ℝ)<a) (hne : a≠0) (ht : 0≤t) :
    (standardLimitKernel a t t)^2=(t^2-2*t^(2*a+2)+t^(4*a+2))/a^2 := by
  by_cases ht0 : t=0
  · subst t
    simp [standardLimitKernel,zero_rpow (show 2*a+1≠0 by linarith),
      zero_rpow (show 2*a+2≠0 by linarith),zero_rpow (show 4*a+2≠0 by linarith)]
  · have htpos : 0<t := lt_of_le_of_ne ht (Ne.symm ht0)
    have h1 : t*t^(2*a+1)=t^(2*a+2) := by
      conv_lhs => lhs; rw [← rpow_one t]
      rw [← rpow_add htpos]
      congr 1
      ring
    have h2 : (t^(2*a+1))^2=t^(4*a+2) := by
      rw [pow_two,← rpow_add htpos]
      congr 1
      ring
    rw [standard_diagonal_formula hne htpos,div_pow]
    congr 1
    linear_combination -2*h1+h2

/-- Exact one-sided energy in the nonlogarithmic case. All three
monomial integrals converge in the entire endpoint-exponent range.
Article: jacobi, Theorem 5.4.
-/
theorem standard_energy_integral_nonzero {a : ℝ} (ha : -(1/2:ℝ)<a) (hne : a≠0) :
    (∫ t in (0:ℝ)..1,(standardLimitKernel a t t)^2)=8/(3*(2*a+3)*(4*a+3)) := by
  have hI1 : IntervalIntegrable (fun t : ℝ => t^2) volume 0 1 :=
    (continuous_id.pow 2).intervalIntegrable _ _
  have hI2 : IntervalIntegrable (fun t : ℝ => t^(2*a+2)) volume 0 1 :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith)
  have hI3 : IntervalIntegrable (fun t : ℝ => t^(4*a+2)) volume 0 1 :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith)
  have he : (∫ t in (0:ℝ)..1,(standardLimitKernel a t t)^2)=
      ∫ t in (0:ℝ)..1,(t^2-2*t^(2*a+2)+t^(4*a+2))/a^2 := by
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t∈Icc (0:ℝ) 1 := by simpa only [uIcc_of_le (by norm_num : (0:ℝ)≤1)] using ht
    exact standard_diagonal_square ha hne ht'.1
  rw [he,intervalIntegral.integral_div,
    intervalIntegral.integral_add (hI1.sub (hI2.const_mul 2)) hI3,
    intervalIntegral.integral_sub hI1 (hI2.const_mul 2),intervalIntegral.integral_const_mul,
    standard_unit_power_integral (by linarith : -1<2*a+2),
    standard_unit_power_integral (by linarith : -1<4*a+2)]
  norm_num only [integral_pow,one_pow,zero_pow (by decide : (3:ℕ)≠0),
    sub_zero,Nat.cast_ofNat]
  field_simp (disch := first | assumption | positivity | linarith)
  ring

/-- The exact logarithmic energy is obtained from the continuous
explicit primitive, without a numerical integral or a parameter-limit premise.
Article: jacobi, Theorem 5.4.
-/
theorem standard_energy_integral_zero :
    (∫ t in (0:ℝ)..1,(standardLimitKernel 0 t t)^2)=8/27 := by
  have he : (∫ t in (0:ℝ)..1,(standardLimitKernel 0 t t)^2)=
      ∫ t in (0:ℝ)..1,4*(t*log t)^2 := by
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t∈Icc (0:ℝ) 1 := by simpa only [uIcc_of_le (by norm_num : (0:ℝ)≤1)] using ht
    change (standardLimitKernel 0 t t)^2=4*(t*log t)^2
    rw [standard_diagonal_zero ht'.1]
    ring
  rw [he,intervalIntegral.integral_const_mul,standard_log_square_integral]
  norm_num

/-- The complete exact one-sided energy formula, including a=0.
Article: jacobi, Theorem 5.4.
-/
theorem standard_energy_integral {a : ℝ} (ha : -(1/2:ℝ)<a) :
    (∫ t in (0:ℝ)..1,(standardLimitKernel a t t)^2)=8/(3*(2*a+3)*(4*a+3)) := by
  by_cases ha0 : a=0
  · subst a
    norm_num only [standard_energy_integral_zero,mul_zero,zero_add]
  · exact standard_energy_integral_nonzero ha ha0

/-- The actual standard Jacobi matrices have exactly the printed cubic
energy limit throughout a>-1/2 and b>-1, with every boundary and integral
obligation discharged.
Article: jacobi, Theorem 5.4.
-/
theorem standard_energy_limit {a b : ℝ} (ha : -(1/2:ℝ)<a) (hb : -1<b) :
    Tendsto (fun N : ℕ => (standardChain a b (by linarith : -1<a) hb N).energy/(N:ℝ)^3)
      atTop (𝓝 (8/(3*(2*a+3)*(4*a+3)))) := by
  rw [← standard_energy_integral ha]
  exact standard_energy_integral_limit ha hb

end
end jacobi.Jacobi
