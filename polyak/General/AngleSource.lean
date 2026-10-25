import polyak.General.Angle

/-! Article: the angle is the polar angle of the actual heavy-ball source symbol. -/
namespace polyak.General
noncomputable section
namespace Tuning

theorem m_threshold_re (q : Tuning) (ω : ℝ) :
    (q.m (Waves.z 0 ω)).re=((1+q.beta)*Real.cos ω-q.A)/q.B := by
  dsimp [m,Waves.z]
  simp only [zero_add,Complex.div_re,Complex.sub_re,
    Complex.add_re,Complex.ofReal_re,Complex.ofReal_im,Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_im,Complex.normSq_apply,mul_zero,zero_mul,add_zero]
  rw [← pow_two,← pow_two,Real.cos_sq_add_sin_sq]
  field_simp [q.B_ne_zero]
  ring

theorem m_threshold_im (q : Tuning) (ω : ℝ) :
    (q.m (Waves.z 0 ω)).im=(1-q.beta)*Real.sin ω/q.B := by
  dsimp [m,Waves.z]
  simp only [zero_add,Complex.div_im,Complex.sub_im,
    Complex.add_im,Complex.ofReal_re,Complex.ofReal_im,Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_im,Complex.normSq_apply,mul_zero,zero_mul,sub_zero,add_zero]
  rw [← pow_two,← pow_two,Real.cos_sq_add_sin_sq]
  field_simp [q.B_ne_zero]
  ring

theorem g_threshold (q : Tuning) (ω : ℝ) :
    1-Complex.normSq (q.m (Waves.z 0 ω)) =
      (2*(1-q.beta)/q.B)*q.Xi (Real.cos ω) := by
  rw [Complex.normSq_apply,q.m_threshold_re,q.m_threshold_im]
  have ht : (Real.sin ω)^2=1-(Real.cos ω)^2 := by nlinarith [Real.sin_sq_add_cos_sq ω]
  dsimp [Xi]
  field_simp [q.B_ne_zero,ne_of_gt (sub_pos.2 q.beta_lt_one)]
  linear_combination -(1-q.beta)^2*ht

theorem threshold_im_pos (q : Tuning) {ω : ℝ} (hω : ω∈Set.Ioo 0 Real.pi) :
    0<(q.m (Waves.z 0 ω)).im := by
  rw [q.m_threshold_im]
  exact div_pos (mul_pos (sub_pos.2 q.beta_lt_one)
    (Real.sin_pos_of_pos_of_lt_pi hω.1 hω.2)) q.B_pos

def polarRadius (q : Tuning) (ω : ℝ) : ℝ := (2*(1-q.beta)/q.B)*q.angleRadius ω
theorem polarRadius_pos (q : Tuning) {ω : ℝ} (hω : ω∈Set.Icc 0 Real.pi) :
    0<q.polarRadius ω := by
  dsimp [polarRadius]
  positivity [q.beta_lt_one,q.B_pos,q.angleRadius_pos hω]
theorem g_polar (q : Tuning) {ω : ℝ} (hω : ω∈Set.Icc 0 Real.pi) :
    1-Complex.normSq (q.m (Waves.z 0 ω))=q.polarRadius ω*Real.cos (q.angle ω) := by
  rw [q.g_threshold,q.cos_angle hω]
  dsimp [polarRadius]
  field_simp [ne_of_gt (q.angleRadius_pos hω)]
theorem im_polar (q : Tuning) {ω : ℝ} (hω : ω∈Set.Icc 0 Real.pi) :
    2*(q.m (Waves.z 0 ω)).im=q.polarRadius ω*Real.sin (q.angle ω) := by
  rw [q.m_threshold_im,q.sin_angle hω]
  dsimp [polarRadius]
  field_simp [ne_of_gt (q.angleRadius_pos hω)]

theorem threshold_polar (q : Tuning) {ω : ℝ} (hω : ω∈Set.Icc 0 Real.pi) :
    (1-q.m (Waves.z 0 ω))*(1+star (q.m (Waves.z 0 ω))) =
      (((2*(1-q.beta)/q.B)*q.angleRadius ω : ℝ):ℂ)*
        Complex.exp (-(q.angle ω : ℂ)*Complex.I) := by
  rw [← real_im_factor,show -(q.angle ω : ℂ)*Complex.I=((-q.angle ω : ℝ):ℂ)*Complex.I by push_cast; ring,
    Complex.exp_ofReal_mul_I]
  apply Complex.ext
  · simp only [Complex.sub_re,Complex.ofReal_re,Complex.mul_re,Complex.ofReal_im,
      Complex.I_re,Complex.I_im,mul_zero,zero_mul,sub_zero,Real.cos_neg,
      Complex.add_re]
    rw [q.g_threshold,q.cos_angle hω]
    field_simp [q.B_ne_zero,ne_of_gt (q.angleRadius_pos hω)]
    norm_num
  · simp only [Complex.sub_im,Complex.ofReal_im,Complex.mul_im,Complex.ofReal_re,
      Complex.I_re,Complex.I_im,mul_zero,zero_mul,add_zero,zero_sub,Real.sin_neg,
      Complex.add_im]
    rw [q.m_threshold_im,q.sin_angle hω]
    field_simp [q.B_ne_zero,ne_of_gt (q.angleRadius_pos hω)]
    norm_num; ring_nf; simp

end Tuning
end
end polyak.General
