import jacobi.Reference.BetaIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
The real integral in Gauss's second summation theorem is evaluated by
t=2*u/(1+u), followed by v=u^2. Both substitutions are monotone on the
closed original interval, so their endpoint-singular weights are allowed.
Source: Euler's beta-integral proof of Gauss's second summation theorem,
DLMF 15.4.28. These are identities of genuine interval integrals.
Use: evaluates the last integral in second_summation_integral without requiring bounded endpoint powers.
-/
namespace jacobi.Reference.Hypergeometric
noncomputable section
open Real Set MeasureTheory
set_option backward.isDefEq.respectTransparency false

/-- The quadratic substitution has exactly the original beta weight as its pullback.
Use: evaluates the last integral in second_summation_integral without requiring bounded endpoint powers.
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
Source: Euler's beta integral with v=u^2.
Proof: at u>0 the powers of u combine to exponent b-1. -/
theorem second_quadratic_pullback (b d : ℝ) {u : ℝ} (hu : u∈Ioo (0:ℝ) 1) :
    2*u* jacobi.Jacobi.weight (b/2-1) (d-1) (u^2)=
      2*u^(b-1)*(1-u^2)^(d-1) := by
  unfold jacobi.Jacobi.weight
  have hp : u*(u^2)^(b/2-1)=u^(b-1) := by
    calc
      _ = u^1*u^(2*(b/2-1)) := by rw [Real.rpow_one,Real.rpow_mul hu.1.le,Real.rpow_two]
      _ = u^(1+2*(b/2-1)) := (Real.rpow_add hu.1 _ _).symm
      _ = _ := by congr 1; ring
  linear_combination 2*(1-u^2)^(d-1)*hp

/-- The fractional linear substitution has exactly the original Euler integrand as its pullback.
Use: reduces second_summation_integral to the quadratic beta integral with all normalizing powers retained.
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
Source: Euler's substitution t=2*u/(1+u) in the proof of DLMF 15.4.28.
Proof: every base is positive on the open interval. Factoring their
quotients leaves one power of 1+u with exponent d-1, which combines
with 1-u to give the genuine quadratic endpoint distance 1-u^2. -/
theorem second_mobius_pullback (b d : ℝ) {u : ℝ} (hu : u∈Ioo (0:ℝ) 1) :
    (2/(1+u)^2)*
      (jacobi.Jacobi.weight (b-1) (d-1) (2*u/(1+u))*
        (1-(2*u/(1+u))/2)^(-(b+2*d-1)))=
      2^b*u^(b-1)*(1-u^2)^(d-1) := by
  -- Positivity licenses each real power identity independently of the endpoint exponents.
  have hq : 0<1+u := by linarith [hu.1]
  have h1 : 1-2*u/(1+u)=(1-u)/(1+u) := by field_simp; ring
  have h2 : 1-(2*u/(1+u))/2=(1+u)⁻¹ := by field_simp; ring
  have h3 : 1-u^2=(1-u)*(1+u) := by ring
  have hp : (1+u)^(b+2*d-1)/((1+u)^2*(1+u)^(b-1)*(1+u)^(d-1))=
      (1+u)^(d-1) := by
    apply (div_eq_iff (by positivity)).mpr
    rw [← Real.rpow_two (1+u),← Real.rpow_add hq,← Real.rpow_add hq,
      ← Real.rpow_add hq]
    congr 1
    ring
  have ht : (2:ℝ)*(2:ℝ)^(b-1)=(2:ℝ)^b := by
    calc
      _ = (2:ℝ)^(1+(b-1)) := by rw [Real.rpow_add (by norm_num : (0:ℝ)<2),Real.rpow_one]
      _ = _ := by congr 1; ring
  unfold jacobi.Jacobi.weight
  rw [h1,h2,h3,Real.div_rpow (mul_nonneg (by norm_num) hu.1.le) hq.le,
    Real.mul_rpow (by norm_num : (0:ℝ)≤2) hu.1.le,
    Real.div_rpow (sub_nonneg.mpr hu.2.le) hq.le,
    Real.inv_rpow hq.le,Real.rpow_neg hq.le,inv_inv,
    Real.mul_rpow (sub_nonneg.mpr hu.2.le) hq.le]
  calc
    _ = (2*(2:ℝ)^(b-1))*u^(b-1)*(1-u)^(d-1)*
        ((1+u)^(b+2*d-1)/((1+u)^2*(1+u)^(b-1)*(1+u)^(d-1))) := by
          field_simp
    _ = _ := by rw [hp,ht]; ring

/-- The original Euler integral at one half has the exact beta value in Gauss's second summation theorem.
Use: combines with euler_integral and Gamma duplication to prove second_summation_real, then the actual complex midpoint reference formulas.
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
Source: Gauss's second summation theorem, DLMF 15.4.28, proved here from Euler's beta integral.
Proof: the monotone substitutions t=2*u/(1+u) and v=u^2 give
2^(b-1)*B(b/2,d). The genuine singular Jacobi-weight integral has
already been evaluated by the community beta--Gamma theorem. -/
theorem second_summation_integral {b d : ℝ} (hb : 0<b) (hd : 0<d) :
    (∫ t in (0:ℝ)..1,jacobi.Jacobi.weight (b-1) (d-1) t*
      (1-t/2)^(-(b+2*d-1)))=
      (2:ℝ)^(b-1)*Real.Gamma (b/2)*Real.Gamma d/Real.Gamma (b/2+d) := by
  -- Monotone change of variables handles the actual singular endpoints without continuity assumptions on the weight.
  let H : ℝ → ℝ := fun t => jacobi.Jacobi.weight (b-1) (d-1) t*(1-t/2)^(-(b+2*d-1))
  have hsub := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (a := (0:ℝ)) (b := 1) (f := fun u => 2*u/(1+u))
    (f' := fun u => 2/(1+u)^2) (g := H)
    (by
      apply ContinuousOn.div (by fun_prop) (by fun_prop)
      intro u hu
      rw [uIcc_of_le (by norm_num : (0:ℝ)≤1)] at hu
      linarith [hu.1])
    (by
      intro u hu
      have hq : 1+u≠0 := by simp only [min_eq_left (by norm_num : (0:ℝ)≤1),max_eq_right (by norm_num : (0:ℝ)≤1),mem_Ioo] at hu; linarith [hu.1]
      convert! (((hasDerivAt_id u).const_mul 2).div ((hasDerivAt_const u 1).add (hasDerivAt_id u)) hq) using 1
      simp
      ring)
    (fun _ _ => by positivity)
  norm_num at hsub
  have hquad := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (a := (0:ℝ)) (b := 1) (f := fun u : ℝ => u^2) (f' := fun u => 2*u)
    (g := jacobi.Jacobi.weight (b/2-1) (d-1)) (by fun_prop)
    (fun u _ => by convert! (hasDerivAt_id u).pow 2 using 1; simp)
    (fun u hu => by simp only [min_eq_left (by norm_num : (0:ℝ)≤1),max_eq_right (by norm_num : (0:ℝ)≤1),mem_Ioo] at hu; linarith [hu.1])
  norm_num only [zero_pow (by norm_num : 2≠0),one_pow] at hquad
  have he : (∫ t in (0:ℝ)..1,H t)=
      (2:ℝ)^(b-1)*(∫ t in (0:ℝ)..1,jacobi.Jacobi.weight (b/2-1) (d-1) t) := by
    rw [← hsub,← hquad,← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
    intro u hu
    have hm := second_mobius_pullback b d hu
    have hq := second_quadratic_pullback b d hu
    have ht : (2:ℝ)^(b-1)*2=(2:ℝ)^b := by
      calc
        _ = (2:ℝ)^((b-1)+1) := by rw [Real.rpow_add (by norm_num : (0:ℝ)<2),Real.rpow_one]
        _ = _ := by congr 1; ring
    dsimp only [Function.comp_apply,H]
    calc
      _ = (2:ℝ)^b*u^(b-1)*(1-u^2)^(d-1) := by rw [mul_comm]; exact hm
      _ = (2:ℝ)^(b-1)*(2*u^(b-1)*(1-u^2)^(d-1)) := by rw [← ht]; ring
      _ = _ := by rw [← hq]; ring
  change (∫ t in (0:ℝ)..1,H t)=_
  rw [he,jacobi_weight_integral (by linarith) (by linarith),
    sub_add_cancel,sub_add_cancel,show b/2-1+(d-1)+2=b/2+d by ring]
  ring

end
end jacobi.Reference.Hypergeometric
