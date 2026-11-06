import nesterov.Quadratic.Basic

/-! Exact Jury tests on any positive circle, with either sign of the determinant. -/
namespace nesterov.Quadratic
noncomputable section

private theorem scaled_quadratic_eq (a q r : ℝ) (hr : r≠0) (w : ℂ) :
    ((r:ℂ)*w)^2-(a:ℂ)*((r:ℂ)*w)+(q:ℂ)=
      (r:ℂ)^2*(w^2-((a/r:ℝ):ℂ)*w+((q/r^2:ℝ):ℂ)) := by
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr hr]

/-- The scaled Jury criterion. The last two real quantities are precisely
the polynomial values at r and -r. -/
theorem roots_lt_radius_iff {a q r : ℝ} (hr : 0<r) :
    (∀ z : ℂ,z^2-(a:ℂ)*z+(q:ℂ)=0 → ‖z‖<r) ↔
      q<r^2 ∧ 0<r^2-a*r+q ∧ 0<r^2+a*r+q := by
  have hr2 : 0<r^2:=sq_pos_of_pos hr
  have hc1 : (a/r)*r^2=a*r:=by field_simp
  have hc2 : (1+q/r^2)*r^2=r^2+q:=by field_simp
  constructor
  · intro h
    have hs : ∀ w : ℂ,w^2-((a/r:ℝ):ℂ)*w+((q/r^2:ℝ):ℂ)=0 → ‖w‖<1 := by
      intro w hw
      have he:=scaled_quadratic_eq a q r hr.ne' w
      rw [hw,mul_zero] at he
      have hn:=h ((r:ℂ)*w) he
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr] at hn
      nlinarith
    obtain ⟨hq,ha⟩:=roots_stable_iff.mp hs
    refine ⟨(div_lt_one hr2).mp hq,?_,?_⟩
    have hp:=mul_lt_mul_of_pos_right (abs_lt.mp ha).2 hr2
    rw [hc1,hc2] at hp
    linarith
    have hm:=mul_lt_mul_of_pos_right (abs_lt.mp ha).1 hr2
    rw [neg_mul,hc1,hc2] at hm
    linarith
  · rintro ⟨hq,hp,hm⟩ z hz
    have ha : |a/r|<1+q/r^2 := by
      rw [abs_lt]
      constructor
      · apply (mul_lt_mul_iff_of_pos_right hr2).mp
        rw [neg_mul,hc1,hc2]
        linarith
      · apply (mul_lt_mul_iff_of_pos_right hr2).mp
        rw [hc1,hc2]
        linarith
    let w : ℂ:=z/(r:ℂ)
    have hw : (r:ℂ)*w=z:=by
      dsimp [w]
      field_simp [Complex.ofReal_ne_zero.mpr hr.ne']
    have he:=scaled_quadratic_eq a q r hr.ne' w
    rw [hw,hz] at he
    have hs : w^2-((a/r:ℝ):ℂ)*w+((q/r^2:ℝ):ℂ)=0:=
      (mul_eq_zero.mp he.symm).resolve_left (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr hr.ne'))
    have hn:=root_norm_lt_one ((div_lt_one hr2).mpr hq) ha hs
    dsimp [w] at hn
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr] at hn
    exact (div_lt_one hr).mp hn

end
end nesterov.Quadratic
