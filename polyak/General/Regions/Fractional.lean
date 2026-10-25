import polyak.General.Regions.PhaseLocking

/-! Source §7: the union of the fractional-cycle inequalities is exactly
the complement of the lag-one convergence region. This is an equality of
the continuous frequency regions, before the later Farey analysis. -/
noncomputable section
namespace polyak.General.Regions

theorem outside_omegaOne_iff_frequency (q : Tuning) :
    ¬OmegaOne q ↔ ∃ ω : ℝ,ω∈Set.Ioo (0:ℝ) Real.pi ∧ q.angle ω≤ω/2 := by
  rw [omegaOne_iff_angle]
  push Not
  constructor
  · rintro ⟨ω,hω,hh⟩
    have hne : ω≠Real.pi:=by
      intro he
      rw [he,q.angle_pi] at hh
      linarith [Real.pi_pos]
    exact ⟨ω,⟨hω.1,lt_of_le_of_ne hω.2 hne⟩,hh⟩
  · rintro ⟨ω,hω,hh⟩
    exact ⟨ω,⟨hω.1,hω.2.le⟩,hh⟩

theorem outside_omegaOne_iff_fractional (q : Tuning) :
    ¬OmegaOne q ↔ ∃ K : ℝ,2<K ∧ q.angle (2*Real.pi/K)≤Real.pi/K := by
  rw [outside_omegaOne_iff_frequency]
  constructor
  · rintro ⟨ω,hω,hh⟩
    let K:=2*Real.pi/ω
    have hK : 2<K:=by dsimp [K]; apply (lt_div_iff₀ hω.1).mpr; linarith [hω.2]
    have he : 2*Real.pi/K=ω:=by dsimp [K]; field_simp [ne_of_gt hω.1,ne_of_gt Real.pi_pos]
    refine ⟨K,hK,?_⟩
    rw [he]
    have he' : Real.pi/K=ω/2:=by rw [←he]; ring
    rwa [he']
  · rintro ⟨K,hK,hh⟩
    have hK0 : 0<K:=by linarith
    refine ⟨2*Real.pi/K,⟨by positivity,?_⟩,?_⟩
    · apply (div_lt_iff₀ hK0).mpr
      nlinarith [Real.pi_pos]
    · convert hh using 1
      ring

end polyak.General.Regions
