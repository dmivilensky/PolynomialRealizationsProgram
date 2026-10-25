import polyak.Levels.Program.PhaseFloors

/-! The lag-one phase floor equals half the frequency, including omega=pi. -/
noncomputable section
namespace polyak.Levels

theorem one_sub_unitPhase_factor (ω : ℝ) :
    1-Complex.exp ((ω:ℂ)*Complex.I)=
      ((2*Real.sin (ω/2):ℝ):ℂ)*Complex.exp (((ω/2-Real.pi/2:ℝ):ℂ)*Complex.I) := by
  have hs := Real.sin_two_mul (ω/2)
  have hc := Real.cos_two_mul (ω/2)
  rw [show 2*(ω/2)=ω by ring] at hs hc
  apply Complex.ext
  · simp only [Complex.sub_re,Complex.one_re,Complex.exp_ofReal_mul_I_re,Complex.mul_re,
      Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    rw [Real.cos_sub,Real.cos_pi_div_two,Real.sin_pi_div_two,mul_zero,mul_one,zero_add]
    nlinarith [Real.sin_sq_add_cos_sq (ω/2)]
  · simp only [Complex.sub_im,Complex.one_im,Complex.exp_ofReal_mul_I_im,Complex.mul_im,
      Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero,zero_sub]
    rw [Real.sin_sub,Real.cos_pi_div_two,Real.sin_pi_div_two,mul_zero,mul_one,zero_sub]
    nlinarith

theorem lagOne_phaseFloor {ω : ℝ} (hω : 0<ω) (hωπ : ω≤Real.pi) :
    (1-Complex.exp ((ω:ℂ)*Complex.I)).arg+Real.pi/2=ω/2 := by
  have hh : 0<Real.sin (ω/2) := Real.sin_pos_of_pos_of_lt_pi (by linarith)
    (by linarith [Real.pi_pos])
  rw [one_sub_unitPhase_factor,Complex.arg_real_mul _ (by linarith : 0<2*Real.sin (ω/2)),
    Complex.arg_exp_mul_I]
  rw [(toIocMod_eq_self Real.two_pi_pos).mpr (show ω/2-Real.pi/2∈Set.Ioc (-Real.pi) (-Real.pi+2*Real.pi) by
    constructor <;> linarith [Real.pi_pos])]
  ring

end polyak.Levels
