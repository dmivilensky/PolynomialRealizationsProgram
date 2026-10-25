import polyak.Levels.Program.Curve
import polyak.Waves.Polyak

/-! Appendix E, equation Lambdapoly, with every signed nonzero lag. -/
noncomputable section
namespace polyak.Levels
open Spectral

theorem cos_int_mul_natAbs (n : ℤ) (ω : ℝ) :
    Real.cos ((n:ℝ)*ω)=Real.cos ((n.natAbs:ℝ)*ω) := by
  obtain ⟨k,rfl|rfl⟩:=n.eq_nat_or_neg
  · rfl
  · simp only [Int.cast_neg,Int.cast_natCast,Int.natAbs_neg,Int.natAbs_natCast,neg_mul,Real.cos_neg]

theorem sin_int_mul_natAbs (n : ℤ) (ω : ℝ) :
    Real.sin ((n:ℝ)*ω)=(n.sign:ℝ)*Real.sin ((n.natAbs:ℝ)*ω) := by
  obtain ⟨k,rfl|rfl⟩:=n.eq_nat_or_neg
  · by_cases hk : k=0
    · simp [hk]
    · have hs : (k:ℤ).sign=1:=Int.sign_eq_one_of_pos (by omega)
      simp only [hs,Int.cast_one,one_mul,Int.cast_natCast,Int.natAbs_natCast]
  · by_cases hk : k=0
    · simp [hk]
    · have hs : (k:ℤ).sign=1:=Int.sign_eq_one_of_pos (by omega)
      simp only [Int.cast_neg,Int.cast_natCast,Int.natAbs_neg,Int.natAbs_natCast,neg_mul,
        Real.sin_neg,Int.sign_neg,hs,Int.cast_one,one_mul]

theorem lag_chebyshev (q : General.Tuning) (n : ℤ) (hn : n≠0)
    (ω : Frequency) (hω : 0<(ω:ℝ) ∧ (ω:ℝ)<Real.pi) :
    (tuningCurve q).lag n ω=Real.sin (q.angle ω)/Real.sin (ω:ℝ)*
      (q.Xi (Real.cos (ω:ℝ))*(1-chebT n.natAbs (Real.cos (ω:ℝ)))-
        (n.sign:ℝ)*(1-(Real.cos (ω:ℝ))^2)*chebU (n.natAbs-1) (Real.cos (ω:ℝ))) := by
  have hs : Real.sin (ω:ℝ)≠0:=(Real.sin_pos_of_pos_of_lt_pi hω.1 hω.2).ne'
  have hθ : Real.sin (q.angle ω)≠0:=
    (Real.sin_pos_of_pos_of_lt_pi (q.angle_mem hω).1 (q.angle_mem hω).2).ne'
  have hc : Real.cos (q.angle ω)=Real.sin (q.angle ω)*
      (q.Xi (Real.cos (ω:ℝ))/Real.sin (ω:ℝ)) := by
    have hh:=q.cot_angle hω
    exact (div_eq_iff hθ).mp hh |>.trans (mul_comm _ _)
  have hk : 1≤n.natAbs:=by have hh:=Int.natAbs_pos.mpr hn; omega
  have hsin : chebU (n.natAbs-1) (Real.cos (ω:ℝ))*Real.sin (ω:ℝ)=
      Real.sin ((n.natAbs:ℝ)*(ω:ℝ)) := by
    have hh:=chebU_sin (n.natAbs-1) (ω:ℝ)
    have he : ((n.natAbs-1:ℕ):ℝ)+1=n.natAbs:=by exact_mod_cast Nat.sub_add_cancel hk
    rwa [he] at hh
  rw [Curve.lag_expand]
  simp only [tuningCurve_apply]
  rw [hc,cos_int_mul_natAbs,←chebT_cos,sin_int_mul_natAbs,←hsin]
  have hid:=Real.sin_sq_add_cos_sq (ω:ℝ)
  field_simp
  rw [show Real.sin (ω:ℝ)^2=1-Real.cos (ω:ℝ)^2 by linarith [hid]]
  ring

end polyak.Levels
