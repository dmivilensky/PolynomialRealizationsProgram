import polyak.Levels.Lattice.Signs
import polyak.Levels.Program.Curve
import polyak.General.Regions.PhaseLocking

/-! The exact lattice formula and its zero lines, for positive and negative lags. -/
noncomputable section
namespace polyak.Levels.Lattice

theorem signed_lag_lattice_formula {θ : ℝ} (hθ : 0<θ) (ω : ℝ) (n : ℤ) :
    lagValue θ ((n:ℝ)*ω)=
      2*Real.sin (Real.pi*(n:ℝ)*xi ω θ/eta θ)*
        Real.sin (Real.pi*((n:ℝ)*xi ω θ-1)/eta θ) := by
  rw [lagValue_eq_sines]
  have he : Real.pi*(n:ℝ)*xi ω θ/eta θ=(n:ℝ)*ω/2:=by
    unfold xi eta
    field_simp
  have he' : Real.pi*((n:ℝ)*xi ω θ-1)/eta θ=(n:ℝ)*ω/2-θ:=by
    unfold xi eta
    field_simp
  rw [he,he']

theorem signed_lag_zero_iff {θ : ℝ} (hθ : 0<θ) (ω : ℝ) (n : ℤ) :
    lagValue θ ((n:ℝ)*ω)=0 ↔
      ∃l : ℤ,(n:ℝ)*xi ω θ-l*eta θ=0 ∨ (n:ℝ)*xi ω θ-l*eta θ=1 := by
  rw [lagValue_eq_sines,mul_eq_zero,mul_eq_zero]
  simp only [show (2:ℝ)≠0 by norm_num,false_or,Real.sin_eq_zero_iff]
  constructor
  · rintro (⟨l,hl⟩|⟨l,hl⟩)
    · refine ⟨l,Or.inl ?_⟩
      unfold xi eta
      field_simp
      nlinarith
    · refine ⟨l,Or.inr ?_⟩
      unfold xi eta
      field_simp
      nlinarith
  · rintro ⟨l,hl|hl⟩
    · left
      refine ⟨l,?_⟩
      unfold xi eta at hl
      field_simp at hl
      nlinarith
    · right
      refine ⟨l,?_⟩
      unfold xi eta at hl
      field_simp at hl
      nlinarith

theorem omegaOne_iff_lattice_halfplane (q : General.Tuning) :
    General.Regions.OmegaOne q ↔ ∀ω : Frequency,xi ω (q.angle ω)<1 := by
  rw [General.Regions.omegaOne_iff_angle]
  constructor
  · intro h ω
    unfold xi
    apply (div_lt_one (by positivity [(tuningCurve q).pos ω] : 0<2*q.angle ω)).mpr
    by_cases hz : (ω:ℝ)=0
    · rw [hz,q.angle_zero]
      linarith [Real.pi_pos]
    · have hh:=h ω ⟨lt_of_le_of_ne ω.property.1 (Ne.symm hz),ω.property.2⟩
      linarith
  · intro h ω hω
    have hh:=h ⟨ω,hω.1.le,hω.2⟩
    unfold xi at hh
    have hp:=(tuningCurve q).pos ⟨ω,hω.1.le,hω.2⟩
    have he:=(div_lt_one (show 0<2*q.angle ω by positivity)).mp hh
    linarith

end polyak.Levels.Lattice
