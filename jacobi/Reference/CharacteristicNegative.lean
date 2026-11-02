import jacobi.Reference.NegativeNormalization
import jacobi.Reference.MidpointSimplicity

/-!
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
The actual reference characteristic has its exact leading coefficient,
deduced from the original beta integral and the proved midpoint product.
The slope comparison uses the genuine negative-energy O(1/y) estimate;
no vertical-strip Gamma or modified-Bessel asymptotic is assumed.
Use: turns the actual reference value's leading asymptotic into the characteristic asymptotic in characteristicTau_negative_leading.
-/
namespace jacobi.Reference
noncomputable section
open Real Set MeasureTheory Filter _root_.Complex
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The true reference midpoint slope, divided by y times the true midpoint value, tends to one on the negative-energy frequency ray.
Use: turns the actual reference value's leading asymptotic into the characteristic asymptotic in characteristicTau_negative_leading.
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
Proof: divide the already proved genuine inverse-y logarithmic
derivative error by y. Its norm is bounded by C/y^2 and hence tends
to zero. All quantities are the actual original midpoint functions. -/
theorem negative_midpoint_slope_ratio {a : ℝ} (ha : -1<a) :
    Tendsto (fun y : ℝ =>
      (waveSlope a (Complex.I*(y:ℂ)) (1/2)).re/
        (y*(wave a (Complex.I*(y:ℂ)) (1/2)).re)) atTop (𝓝 1) := by
  -- The proved original quotient estimate supplies the actual uniform remainder, without an asymptotic premise.
  obtain ⟨C,_,hbound⟩ := negative_midpoint_asymptotic ha
  let r : ℝ → ℝ := fun y => (waveSlope a (Complex.I*(y:ℂ)) (1/2)).re/
    (wave a (Complex.I*(y:ℂ)) (1/2)).re
  have hl : Tendsto (fun y : ℝ => C/y/y) atTop (𝓝 0) :=
    (tendsto_id.const_div_atTop C).div_atTop tendsto_id
  have herr : Tendsto (fun y : ℝ => (r y-y)/y) atTop (𝓝 0) := by
    apply squeeze_zero_norm' ?_ hl
    filter_upwards [hbound,eventually_gt_atTop (0:ℝ)] with y hy hyp
    rw [Real.norm_eq_abs,abs_div,abs_of_pos hyp]
    exact div_le_div_of_nonneg_right hy hyp.le
  have hr := herr.add_const 1
  norm_num only [zero_add] at hr
  apply hr.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with y hy
  have he : (r y-y)/y+1=r y/y := by field_simp; ring
  rw [he]
  dsimp [r]
  rw [div_div,mul_comm _ y]

/-- The literal reference characteristic has its exact leading coefficient on the shifted negative-energy axis.
Use: fixes the reference half of the relative characteristic normalization in Appendix C.2 and the normalized parity residue formulas.
Article: jacobi, Appendix C.2 (norming ratios).
Proof: the original beta integral gives the exact leading midpoint
value. The actual midpoint slope divided by y times that value tends
to one. Substitute both limits in the proved exact product
2*a_0*b_0=kappa*Delta_tau; positive-base powers and exponentials
give the stated leading normalization. -/
theorem characteristicTau_negative_leading {a : ℝ} (ha : -1<a) :
    Tendsto (fun y : ℝ => y^(2*gamma a-1)*Real.exp (-y)*
      (characteristicTau a ((jacobi.Jacobi.endpointCorrection a-y^2:ℝ):ℂ)).re)
      atTop (𝓝 ((Real.Gamma (gamma a)/((2:ℝ)^(gamma a)*betaNormalization (gamma a)))^2/
        (Real.pi^2*normConstant a))) := by
  -- All leading quantities are limits of the same actual reference functions and their genuine spatial derivatives.
  let A : ℝ → ℝ := fun y => (wave a (Complex.I*(y:ℂ)) (1/2)).re
  let B : ℝ → ℝ := fun y => (waveSlope a (Complex.I*(y:ℂ)) (1/2)).re
  let κ := 2*Real.pi^2*normConstant a
  have hκ : 0<κ := by dsimp [κ]; positivity [normConstant_pos ha]
  have hA (y : ℝ) : 0<A y := wave_imaginary_pos ha y (by norm_num)
  have hf := wave_imaginary_leading ha (t := (1/2:ℝ)) (by norm_num)
  have hF : Tendsto (fun y : ℝ => y^(gamma a)*Real.exp (-y/2)*A y) atTop
      (𝓝 (Real.Gamma (gamma a)/((2:ℝ)^(gamma a)*betaNormalization (gamma a)))) := by
    convert! hf using 1
    funext y
    rw [show -(1/2*y)= -y/2 by ring]
  have hq := negative_midpoint_slope_ratio ha
  have hlim := ((hF.pow 2).mul hq).const_mul (2/κ)
  have hconst : (2/κ)*((Real.Gamma (gamma a)/((2:ℝ)^(gamma a)*betaNormalization (gamma a)))^2*1)=
      (Real.Gamma (gamma a)/((2:ℝ)^(gamma a)*betaNormalization (gamma a)))^2/
        (Real.pi^2*normConstant a) := by dsimp [κ]; ring
  rw [hconst] at hlim
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with y hy
  have hvalue : ((A y:ℝ):ℂ)=wave a (Complex.I*(y:ℂ)) (1/2) := by
    have hr := solution_real a (jacobi.Jacobi.endpointCorrection a-y^2) (1/2)
    simpa only [solution_negative_eq_wave] using hr
  have hslope : ((B y:ℝ):ℂ)=waveSlope a (Complex.I*(y:ℂ)) (1/2) := by
    have hr := solutionSlope_real a (jacobi.Jacobi.endpointCorrection a-y^2) (t := (1/2:ℝ)) (by norm_num)
    simpa only [solutionSlope_negative_eq_wave a y (by norm_num : (1/2:ℝ)∈Ioo (0:ℝ) 1)] using hr
  have hp := solution_midpoint_product ha ((jacobi.Jacobi.endpointCorrection a-y^2:ℝ):ℂ)
  rw [solution_negative_eq_wave,solutionSlope_negative_eq_wave a y (by norm_num : (1/2:ℝ)∈Ioo (0:ℝ) 1),
    ← hvalue,← hslope] at hp
  have hpr := congrArg Complex.re hp
  have he : 2*A y*B y=κ*(characteristicTau a ((jacobi.Jacobi.endpointCorrection a-y^2:ℝ):ℂ)).re := by
    simpa only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,Complex.re_ofNat,
      Complex.im_ofNat,zero_mul,mul_zero,sub_zero] using hpr
  have hchar : (characteristicTau a ((jacobi.Jacobi.endpointCorrection a-y^2:ℝ):ℂ)).re=
      2*A y*B y/κ := (eq_div_iff hκ.ne').mpr (by linear_combination -he)
  have hpow : (y^(gamma a))^2=y^(2*gamma a-1)*y := by
    rw [← Real.rpow_two (y^(gamma a)),← Real.rpow_mul hy.le,
      ← Real.rpow_add_one hy.ne',show 2*gamma a-1+1=gamma a*2 by ring]
  have hexp : (Real.exp (-y/2))^2=Real.exp (-y) := by
    rw [pow_two,← Real.exp_add,show -y/2+(-y/2)= -y by ring]
  change (2/κ)*((y^(gamma a)*Real.exp (-y/2)*A y)^2*(B y/(y*A y)))=_
  rw [hchar,mul_pow,mul_pow,hpow,hexp]
  field_simp [(hA y).ne',hy.ne',hκ.ne']

end
end jacobi.Reference
