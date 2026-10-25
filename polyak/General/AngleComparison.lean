import polyak.General.Angle

/-! Article: lem:cubic, the exact angle/lag-one comparison, including ω=π. -/
namespace polyak.General
noncomputable section

theorem cot_strictAnti {a b : ℝ} (ha : a∈Set.Ioo 0 Real.pi) (hb : b∈Set.Ioo 0 Real.pi) :
    Real.cos a/Real.sin a < Real.cos b/Real.sin b ↔ b<a := by
  have hsa := Real.sin_pos_of_pos_of_lt_pi ha.1 ha.2
  have hsb := Real.sin_pos_of_pos_of_lt_pi hb.1 hb.2
  rw [div_lt_div_iff₀ hsa hsb]
  constructor
  · intro h
    by_contra hab
    have hab : a≤b := le_of_not_gt hab
    have hs := Real.sin_nonneg_of_nonneg_of_le_pi (show 0≤b-a by linarith)
      (show b-a≤Real.pi by linarith [ha.1,hb.2])
    rw [Real.sin_sub] at hs
    nlinarith
  · intro h
    have hs := Real.sin_pos_of_pos_of_lt_pi (show 0<a-b by linarith)
      (show a-b<Real.pi by linarith [hb.1,ha.2])
    rw [Real.sin_sub] at hs
    nlinarith

theorem cot_half {ω : ℝ} (hω : ω∈Set.Ioo 0 Real.pi) :
    Real.cos (ω/2)/Real.sin (ω/2)=(1+Real.cos ω)/Real.sin ω := by
  have hs := ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hω.1 hω.2)
  have hh := ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (show 0<ω/2 by linarith [hω.1])
    (show ω/2<Real.pi by linarith [hω.2,Real.pi_pos]))
  have hc := Real.cos_two_mul (ω/2)
  have hsin := Real.sin_two_mul (ω/2)
  rw [show 2*(ω/2)=ω by ring] at hc hsin
  field_simp [hs,hh]
  rw [hc,hsin]
  ring

namespace Tuning
theorem angle_gt_half_iff (q : Tuning) {ω : ℝ} (hω : ω∈Set.Ioc 0 Real.pi) :
    ω/2<q.angle ω ↔ 0<q.L (Real.cos ω) := by
  rcases eq_or_lt_of_le hω.2 with he|he
  · subst ω
    rw [q.angle_pi,Real.cos_pi]
    exact iff_of_true (by linarith [Real.pi_pos]) q.L_neg_one_pos
  · have hi : ω∈Set.Ioo 0 Real.pi := ⟨hω.1,he⟩
    have hh : ω/2∈Set.Ioo 0 Real.pi := ⟨by linarith [hi.1],by linarith [hi.2,Real.pi_pos]⟩
    rw [← cot_strictAnti (q.angle_mem hi) hh,q.cot_angle hi,cot_half hi,
      div_lt_div_iff_of_pos_right (Real.sin_pos_of_pos_of_lt_pi hi.1 hi.2),q.L_eq_Xi]
    have hp : 0<(q.y-q.x)*(1-q.beta) := mul_pos (sub_pos.2 q.x_lt_y) (sub_pos.2 q.beta_lt_one)
    rw [mul_pos_iff_of_pos_left hp]
    constructor <;> intro h <;> linarith
end Tuning
end
end polyak.General
