import polyak.Levels.Geometry.TuningCotangent

/-! A finite upper bound for the true cotangent on the entire open
frequency interval, obtained from its proved concavity and central tangent. -/
noncomputable section
namespace polyak.Levels.Geometry
open General Set

def cotangentUpper (q : Tuning) : ℝ :=
  cotangent q (Real.pi/2)+|cotangentFirst q (Real.pi/2)| *Real.pi

theorem cotangent_le_upper (q : Tuning) {ω : ℝ} (hω : ω∈Ioo 0 Real.pi) :
    cotangent q ω≤cotangentUpper q := by
  have hm : Real.pi/2∈Ioo 0 Real.pi := by constructor <;> linarith [Real.pi_pos]
  have hc:=(cotangent_strictConcaveOn q).concaveOn
  have hd:=hasDerivAt_cotangent q hm
  have ht : cotangent q ω≤cotangent q (Real.pi/2)+cotangentFirst q (Real.pi/2)*(ω-Real.pi/2) := by
    rcases lt_trichotomy ω (Real.pi/2) with h|h|h
    · have hh:=hc.le_slope_of_hasDerivAt hω hm h hd
      rw [slope_def_field] at hh
      have hx:0<Real.pi/2-ω:=sub_pos.mpr h
      have hb:=(le_div_iff₀ hx).mp hh
      linarith
    · simp only [h,sub_self,mul_zero,add_zero,le_refl]
    · have hh:=hc.slope_le_of_hasDerivAt hm hω h hd
      rw [slope_def_field] at hh
      have hx:0<ω-Real.pi/2:=sub_pos.mpr h
      have hb:=(div_le_iff₀ hx).mp hh
      linarith
  have hab : |ω-Real.pi/2|≤Real.pi := by rw [abs_le]; constructor <;> linarith [hω.1,hω.2,Real.pi_pos]
  have hprod : cotangentFirst q (Real.pi/2)*(ω-Real.pi/2)≤|cotangentFirst q (Real.pi/2)| *Real.pi :=
    (le_abs_self _).trans (by rw [abs_mul]; exact mul_le_mul_of_nonneg_left hab (abs_nonneg _))
  exact ht.trans (by simpa only [cotangentUpper] using add_le_add_right hprod (cotangent q (Real.pi/2)))

theorem cotangent_bddAbove (q : Tuning) :
    ∃ H : ℝ,∀ω∈Ioo 0 Real.pi,cotangent q ω≤H := ⟨cotangentUpper q,fun _ hω=>cotangent_le_upper q hω⟩

end polyak.Levels.Geometry
