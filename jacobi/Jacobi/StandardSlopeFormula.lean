import jacobi.Jacobi.StandardSlopeMesh
import jacobi.Applications.StandardJacobi
import jacobi.Applications.FlowConstants
import jacobi.Analysis.PrefixMesh

/-!
Exact evaluation of the continuum initial resolvent-flow derivative.
The triangular Green integral is reduced to elementary power integrals;
the logarithmic parameter is evaluated with a continuous primitive.
Use: StandardDescent combines this value with the actual finite derivative
limit and the global Taylor estimate to obtain strict energy improvement.
Article: jacobi, Theorem 5.6.
Article role: evaluation of D_alpha, including the logarithmic parameter, from the triangular Green
integral.
-/
namespace jacobi.Jacobi
noncomputable section
open Real Set Filter MeasureTheory jacobi.Analysis
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The squared off-diagonal kernel separates into one endpoint power
and the diagonal value. Squaring removes all square-root choices.
Article: jacobi, Theorem 5.6.
-/
theorem standard_kernel_square {a t u : ℝ} (ht : 0<t) (hu : 0≤u) (hut : u≤t) :
    (standardLimitKernel a t u)^2=
      u^(2*a+1)/t^(2*a+1)*(standardLimitKernel a t t)^2 := by
  have hp : 0<t^(2*a+1) := rpow_pos_of_pos ht _
  have hup : 0≤u^(2*a+1) := rpow_nonneg hu _
  simp only [standardLimitKernel,max_eq_left hut,max_self]
  simp only [mul_pow,sq_sqrt (mul_nonneg hp.le hup),sq_sqrt (mul_nonneg hp.le hp.le)]
  field_simp [hp.ne']

/-- The cutoff in the limiting derivative is exactly integration over
the physical triangle, including its zero endpoint.
Article: jacobi, Theorem 5.6.
-/
theorem standard_slope_triangle {a t : ℝ} (ht : t∈Icc (0:ℝ) 1) :
    (∫ u in (0:ℝ)..1,if u<t then
      4*(standardLimitKernel a t t-standardLimitKernel a u u)*(standardLimitKernel a t u)^2 else 0)=
    ∫ u in (0:ℝ)..t,
      4*(standardLimitKernel a t t-standardLimitKernel a u u)*(standardLimitKernel a t u)^2 :=
  unit_cutoff_integral _ ht

/-- The power primitive on a positive initial interval. It is used only
with exponents greater than minus one, so every integral is genuine.
Article: jacobi, Theorem 5.6.
-/
theorem standard_prefix_power {q t : ℝ} (hq : -1<q) (_ht : 0≤t) :
    (∫ u in (0:ℝ)..t,u^q)=t^(q+1)/(q+1) := by
  rw [integral_rpow (Or.inl hq),zero_rpow (show q+1≠0 by linarith),sub_zero]

/-- The weighted diagonal difference has a two-power primitive.
This evaluates the inner triangle integral before expanding the outer one.
Article: jacobi, Theorem 5.6.
-/
theorem standard_slope_inner_nonzero {a t : ℝ} (ha : -(1/2:ℝ)<a)
    (hne : a≠0) (ht : 0<t) :
    (∫ u in (0:ℝ)..t,(standardLimitKernel a t t-standardLimitKernel a u u)*u^(2*a+1))=
      (t^(2*a+3)/(2*a+3)-(2*a+1)*t^(4*a+3)/(4*a+3))/(a*(2*a+2)) := by
  have hp : 0<2*a+1 := by linarith
  have hI (q : ℝ) (hq : -1<q) : IntervalIntegrable (fun u : ℝ => u^q) volume 0 t :=
    intervalIntegral.intervalIntegrable_rpow' hq
  have he : (∫ u in (0:ℝ)..t,(standardLimitKernel a t t-standardLimitKernel a u u)*u^(2*a+1))=
      ∫ u in (0:ℝ)..t,((t-t^(2*a+1))*u^(2*a+1)-u^(2*a+2)+u^(4*a+2))/a := by
    apply intervalIntegral.integral_congr_uIoo
    intro u hmem
    have hu0 : 0<u := by simpa only [min_eq_left ht.le] using hmem.1
    dsimp only
    rw [standard_diagonal_formula hne ht,standard_diagonal_formula hne hu0]
    have h1 : u*u^(2*a+1)=u^(2*a+2) := by
      conv_lhs => lhs; rw [← rpow_one u]
      rw [← rpow_add hu0]
      congr 1
      ring
    have h2 : u^(2*a+1)*u^(2*a+1)=u^(4*a+2) := by
      rw [← rpow_add hu0]
      congr 1
      ring
    rw [← sub_div,div_mul_eq_mul_div]
    congr 1
    simp only [sub_mul,h1,h2]
    ring
  rw [he,intervalIntegral.integral_div,
    intervalIntegral.integral_add ((hI _ (by linarith)).const_mul _ |>.sub (hI _ (by linarith))) (hI _ (by linarith)),
    intervalIntegral.integral_sub ((hI _ (by linarith)).const_mul _) (hI _ (by linarith)),
    intervalIntegral.integral_const_mul,
    standard_prefix_power (by linarith : -1<2*a+1) ht.le,
    standard_prefix_power (by linarith : -1<2*a+2) ht.le,
    standard_prefix_power (by linarith : -1<4*a+2) ht.le]
  have h1 : t*t^(2*a+1+1)=t^(2*a+3) := by
    conv_lhs => lhs; rw [← rpow_one t]
    rw [← rpow_add ht]
    congr 1
    ring
  have h2 : t^(2*a+1)*t^(2*a+1+1)=t^(4*a+3) := by
    rw [← rpow_add ht]
    congr 1
    ring
  have h3 : 2*a+2+1=2*a+3 := by ring
  have h4 : 4*a+2+1=4*a+3 := by ring
  rw [h3,h4]
  simp only [← mul_div_assoc,sub_mul,h1,h2]
  field_simp (disch := first | assumption | positivity | linarith)
  ring

/-- Expanding the evaluated triangular integral leaves four integrable
powers. Their exponents stay positive throughout the admissible range.
Article: jacobi, Theorem 5.6.
-/
theorem standard_slope_integrand_nonzero {a t : ℝ} (ha : -(1/2:ℝ)<a)
    (hne : a≠0) (ht : t∈Ioc (0:ℝ) 1) :
    (∫ u in (0:ℝ)..1,if u<t then
      4*(standardLimitKernel a t t-standardLimitKernel a u u)*(standardLimitKernel a t u)^2 else 0)=
    4/(a^3*(2*a+2))*(t^4/(2*a+3)-
      ((2*a+1)/(4*a+3)+2/(2*a+3))*t^(2*a+4)+
      (2*(2*a+1)/(4*a+3)+1/(2*a+3))*t^(4*a+4)-
      (2*a+1)/(4*a+3)*t^(6*a+4)) := by
  rw [standard_slope_triangle ⟨ht.1.le,ht.2⟩]
  have he : (∫ u in (0:ℝ)..t,
      4*(standardLimitKernel a t t-standardLimitKernel a u u)*(standardLimitKernel a t u)^2)=
    (4*(standardLimitKernel a t t)^2/t^(2*a+1))*
      ∫ u in (0:ℝ)..t,(standardLimitKernel a t t-standardLimitKernel a u u)*u^(2*a+1) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr_uIoo
    intro u hu
    rw [uIoo_of_le ht.1.le] at hu
    have hu' := hu
    dsimp only
    rw [standard_kernel_square ht.1 hu'.1.le hu'.2.le]
    ring
  rw [he,standard_slope_inner_nonzero ha hne ht.1,standard_diagonal_formula hne ht.1]
  have hp : t^(2*a+1)≠0 := (rpow_pos_of_pos ht.1 _).ne'
  have hpow (m n : ℕ) : t^((2*a+1)*(m:ℝ)+(n:ℝ))=(t^(2*a+1))^m*t^n := by
    rw [rpow_add ht.1,rpow_mul ht.1.le,rpow_natCast,rpow_natCast]
  have h1 := hpow 1 2
  have h2 := hpow 2 1
  have h3 := hpow 1 3
  have h4 := hpow 2 2
  have h5 := hpow 3 1
  norm_num only [Nat.cast_ofNat,Nat.cast_one,pow_one,mul_one,one_mul] at h1 h2 h3 h4 h5
  have e1 : (2*a+1)+2=2*a+3 := by ring
  have e2 : (2*a+1)*2+1=4*a+3 := by ring
  have e3 : (2*a+1)+3=2*a+4 := by ring
  have e4 : (2*a+1)*2+2=4*a+4 := by ring
  have e5 : (2*a+1)*3+1=6*a+4 := by ring
  rw [e1] at h1
  rw [e2] at h2
  rw [e3] at h3
  rw [e4] at h4
  rw [e5] at h5
  rw [h1,h2,h3,h4,h5]
  field_simp (disch := first | assumption | positivity | linarith)
  ring

/-- Exact initial derivative in the nonlogarithmic case. The proof
integrates the four genuine monomials and simplifies their rational sum.
Article: jacobi, Theorem 5.6.
-/
theorem standard_slope_integral_nonzero {a : ℝ} (ha : -(1/2:ℝ)<a) (hne : a≠0) :
    standardSlopeIntegral a=jacobi.Applications.standardSlope a := by
  have hI (q : ℝ) (hq : -1<q) : IntervalIntegrable (fun t : ℝ => t^q) volume 0 1 :=
    intervalIntegral.intervalIntegrable_rpow' hq
  have hI4 : IntervalIntegrable (fun t : ℝ => t^4) volume 0 1 :=
    (continuous_id.pow 4).intervalIntegrable _ _
  have he : standardSlopeIntegral a=∫ t in (0:ℝ)..1,
      4/(a^3*(2*a+2))*(t^4/(2*a+3)-
      ((2*a+1)/(4*a+3)+2/(2*a+3))*t^(2*a+4)+
      (2*(2*a+1)/(4*a+3)+1/(2*a+3))*t^(4*a+4)-
      (2*a+1)/(4*a+3)*t^(6*a+4)) := by
    apply intervalIntegral.integral_congr_uIoo
    intro t ht
    rw [uIoo_of_le (by norm_num : (0:ℝ)≤1)] at ht
    exact standard_slope_integrand_nonzero ha hne
      (by simpa only [min_eq_left (by norm_num : (0:ℝ)≤1),max_eq_right (by norm_num : (0:ℝ)≤1)] using ⟨ht.1,ht.2.le⟩)
  rw [he,intervalIntegral.integral_const_mul,
    intervalIntegral.integral_sub
      (((hI4.div_const _).sub ((hI _ (by linarith)).const_mul _)).add ((hI _ (by linarith)).const_mul _))
      ((hI _ (by linarith)).const_mul _),
    intervalIntegral.integral_add ((hI4.div_const _).sub ((hI _ (by linarith)).const_mul _))
      ((hI _ (by linarith)).const_mul _),
    intervalIntegral.integral_sub (hI4.div_const _) ((hI _ (by linarith)).const_mul _),
    intervalIntegral.integral_div,intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,
    standard_unit_power_integral (by linarith : -1<2*a+4),
    standard_unit_power_integral (by linarith : -1<4*a+4),
    standard_unit_power_integral (by linarith : -1<6*a+4)]
  norm_num only [integral_pow,one_pow,zero_pow (by decide : (5:ℕ)≠0),sub_zero,Nat.cast_ofNat]
  unfold jacobi.Applications.standardSlope
  field_simp (disch := first | assumption | positivity | linarith)
  ring

/-- A continuous primitive evaluates the only prefix logarithmic moment
needed at parameter zero. The endpoint contributes exactly zero.
Article: jacobi, Theorem 5.6.
-/
theorem standard_prefix_log {t : ℝ} (ht : 0≤t) :
    (∫ u in (0:ℝ)..t,u*(u*log u))=t^2*(t*log t)/3-t^3/9 := by
  let F : ℝ → ℝ := fun x => x^2*(x*log x)/3-x^3/9
  have hc : Continuous F :=
    ((continuous_id.pow 2).mul continuous_mul_log |>.div_const 3).sub
      ((continuous_id.pow 3).div_const 9)
  have hd (x : ℝ) (hx : x∈Ioo (0:ℝ) t) : HasDerivAt F (x*(x*log x)) x := by
    have h := ((((hasDerivAt_id x).pow 2).mul (hasDerivAt_mul_log hx.1.ne')).div_const 3).sub
      (((hasDerivAt_id x).pow 3).div_const 9)
    convert h using 1
    · rfl
    · dsimp only [Pi.mul_apply,Pi.pow_apply,Pi.div_apply,id_eq]
      ring
  have hI : IntervalIntegrable (fun x : ℝ => x*(x*log x)) volume 0 t :=
    (continuous_id.mul continuous_mul_log).intervalIntegrable _ _
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht hc.continuousOn hd hI
  simpa [F] using h

/-- The logarithmic triangle integral is a polynomial in the continuous
quantity t*log(t). This avoids any singular boundary integration.
Article: jacobi, Theorem 5.6.
-/
theorem standard_slope_integrand_zero {t : ℝ} (ht : t∈Ioc (0:ℝ) 1) :
    (∫ u in (0:ℝ)..1,if u<t then
      4*(standardLimitKernel 0 t t-standardLimitKernel 0 u u)*(standardLimitKernel 0 t u)^2 else 0)=
      -(16/3:ℝ)*t*(t*log t)^3-(32/9:ℝ)*t^2*(t*log t)^2 := by
  rw [standard_slope_triangle ⟨ht.1.le,ht.2⟩]
  have he : (∫ u in (0:ℝ)..t,
      4*(standardLimitKernel 0 t t-standardLimitKernel 0 u u)*(standardLimitKernel 0 t u)^2)=
      32*t*(log t)^2*(∫ u in (0:ℝ)..t,u*(u*log u)-(t*log t)*u) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr_uIoo
    intro u hu
    have hu0 : 0<u := by simpa only [min_eq_left ht.1.le] using hu.1
    have hut : u≤t := by
      have h : u<t := by simpa only [max_eq_right ht.1.le] using hu.2
      exact h.le
    dsimp only
    rw [standard_kernel_square ht.1 hu0.le hut,
      standard_diagonal_zero ht.1.le,standard_diagonal_zero hu0.le]
    norm_num only [mul_zero,zero_add,rpow_one]
    field_simp
    ring
  have hI1 : IntervalIntegrable (fun u : ℝ => u*(u*log u)) volume 0 t :=
    (continuous_id.mul continuous_mul_log).intervalIntegrable _ _
  have hI2 : IntervalIntegrable (fun u : ℝ => (t*log t)*u) volume 0 t :=
    continuous_id.intervalIntegrable _ _ |>.const_mul _
  rw [he,intervalIntegral.integral_sub hI1 hI2,
    intervalIntegral.integral_const_mul,standard_prefix_log ht.1.le,integral_id]
  ring

/-- The exact logarithmic initial slope, obtained from two already
proved logarithmic moments rather than a limiting parameter argument.
Article: jacobi, Theorem 5.6.
-/
theorem standard_slope_integral_zero :
    standardSlopeIntegral 0=jacobi.Applications.standardSlope 0 := by
  have he : standardSlopeIntegral 0=∫ t in (0:ℝ)..1,
      -(16/3:ℝ)*t*(t*log t)^3-(32/9:ℝ)*t^2*(t*log t)^2 := by
    apply intervalIntegral.integral_congr_uIoo
    intro t ht
    rw [uIoo_of_le (by norm_num : (0:ℝ)≤1)] at ht
    exact standard_slope_integrand_zero
      (by simpa only [min_eq_left (by norm_num : (0:ℝ)≤1),max_eq_right (by norm_num : (0:ℝ)≤1)] using ⟨ht.1,ht.2.le⟩)
  have hI (m k : ℕ) : IntervalIntegrable (fun t : ℝ => t^m*(t*log t)^k) volume 0 1 :=
    ((continuous_id.pow m).mul (continuous_mul_log.pow k)).intervalIntegrable _ _
  rw [he]
  simp_rw [mul_assoc]
  rw [intervalIntegral.integral_sub
    (by simpa only [pow_one,mul_assoc] using (hI 1 3).const_mul (-(16/3:ℝ)))
    (by simpa only [mul_assoc] using (hI 2 2).const_mul (32/9:ℝ)),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul]
  have h1 := logMoment_formula 1 3
  have h2 := logMoment_formula 2 2
  norm_num [logMoment] at h1 h2
  rw [h1,h2]
  norm_num [jacobi.Applications.standardSlope]

/-- Exact evaluation of the actual initial-slope continuum integral,
including the logarithmic parameter and the vanishing symmetric slope.
Article: jacobi, Theorem 5.6.
-/
theorem standard_slope_integral {a : ℝ} (ha : -(1/2:ℝ)<a) :
    standardSlopeIntegral a=jacobi.Applications.standardSlope a := by
  by_cases h : a=0
  · subst a
    exact standard_slope_integral_zero
  · exact standard_slope_integral_nonzero ha h

end
end jacobi.Jacobi
