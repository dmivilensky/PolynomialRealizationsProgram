import polyak.Levels.Geometry.DipMass

/-! The positive and zero sets of the lag-one inequality. -/
noncomputable section
namespace polyak.Levels.Geometry
open Set

theorem lag_one_pos_iff (Θ : Curve) (ω : Frequency) :
    0<Θ.lag 1 ω ↔ ω∈dip Θ := by
  constructor
  · intro h
    by_contra hn
    have hθ : (ω:ℝ)/2≤Θ ω:=le_of_not_gt hn
    by_cases hz : ω=frequencyZero
    · simp only [hz,Curve.lag_at_zero,lt_self_iff_false] at h
    · have hω : 0<(ω:ℝ):=lt_of_le_of_ne ω.property.1 (fun he=>hz (Subtype.ext he.symm))
      rcases eq_or_lt_of_le hθ with he|he
      · have hl : Θ.lag 1 ω=0 := by
          simp only [Curve.lag,Int.cast_one,one_mul,←he]
          rw [show (ω:ℝ)-(ω:ℝ)/2=(ω:ℝ)/2 by ring]
          exact sub_self _
        linarith
      · have hl:=(lag_one_neg_iff Θ ω).mpr ⟨hω,he⟩
        linarith
  · intro h
    have hθ : Θ ω<(ω:ℝ)/2:=h
    have harg : (ω:ℝ)-Θ ω∈Icc 0 Real.pi:=⟨by linarith [Θ.pos ω],by linarith [ω.property.2,Θ.pos ω]⟩
    have hh:=Real.strictAntiOn_cos ⟨(Θ.pos ω).le,Θ.le_pi ω⟩ harg (by linarith : Θ ω<(ω:ℝ)-Θ ω)
    simpa only [Curve.lag,Int.cast_one,one_mul,sub_pos] using hh

theorem lag_one_zero_on_closedDip_boundary (Θ : Curve) {ω : Frequency}
    (hc : ω∈closedDip Θ) (hd : ω∉dip Θ) : Θ.lag 1 ω=0 := by
  have he : Θ ω=(ω:ℝ)/2:=le_antisymm hc (le_of_not_gt hd)
  simp only [Curve.lag,Int.cast_one,one_mul,he]
  rw [show (ω:ℝ)-(ω:ℝ)/2=(ω:ℝ)/2 by ring]
  exact sub_self _

end polyak.Levels.Geometry
