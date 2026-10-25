import polyak.Levels.Lattice.Atoms
import polyak.General.Regions.PhaseLocking

/-! Exact lattice zero lines and parent incidences, and the lag-one half
plane. These statements retain every signed integer lag. -/
noncomputable section
namespace polyak.Levels.Lattice
open Set

theorem signed_lag_zero_iff_integer_lines {θ ω : ℝ} (hθ : 0<θ) (n : ℤ) :
    lagValue θ ((n:ℝ)*ω)=0 ↔
      (∃ l : ℤ,(n:ℝ)*xi ω θ-l*eta θ=0) ∨
      (∃ l : ℤ,(n:ℝ)*xi ω θ-l*eta θ=1) := by
  rw [lagValue_eq_sines]
  have hzero : 2*Real.sin ((n:ℝ)*ω/2)*Real.sin ((n:ℝ)*ω/2-θ)=0 ↔
      Real.sin ((n:ℝ)*ω/2)=0 ∨ Real.sin ((n:ℝ)*ω/2-θ)=0 := by
    rw [mul_eq_zero,mul_eq_zero]
    norm_num
  rw [hzero,Real.sin_eq_zero_iff,Real.sin_eq_zero_iff]
  apply or_congr
  · apply exists_congr
    intro l
    unfold xi eta
    constructor <;> intro h <;> field_simp at h ⊢ <;> nlinarith
  · apply exists_congr
    intro l
    unfold xi eta
    constructor <;> intro h <;> field_simp at h ⊢ <;> nlinarith

/-- Both signed parent lines, including their uniquely determined integer
intercepts, are the complete list below the period. -/
theorem FareyParents.small_line_iff {j k : ℤ} (P : FareyParents j k)
    (n l : ℤ) (hn : |n|<k) : n*j-l*k=1 ↔
      (n=P.b ∧ l=P.a) ∨ (n= -P.d ∧ l= -P.c) := by
  constructor
  · intro h
    rcases (P.small_incidence_iff n hn).mp ⟨l,h⟩ with he|he
    · left
      refine ⟨he,?_⟩
      have hh : (l-P.a)*k=0 := by rw [he] at h; linear_combination P.lower_bezout-h
      exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_right P.period_pos.ne')
    · right
      refine ⟨he,?_⟩
      have hh : (l-(-P.c))*k=0 := by rw [he] at h; linear_combination P.upper_bezout-h
      exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_right P.period_pos.ne')
  · rintro (⟨rfl,rfl⟩|⟨rfl,rfl⟩)
    · exact P.lower_bezout
    · exact P.upper_bezout

/-- The graph lies in xi<1 exactly when it lies strictly above omega/2. -/
theorem xi_lt_one_iff {θ ω : ℝ} (hθ : 0<θ) : xi ω θ<1 ↔ ω/2<θ := by
  unfold xi
  rw [div_lt_one (by positivity : 0<2*θ)]
  constructor <;> intro h <;> linarith

/-- Primitive phase-locking points have their literal integral coordinates. -/
theorem rational_lattice_point {j k : ℕ} (hk : 0<k) :
    xi (2*Real.pi*j/k) (Real.pi/k)=j ∧ eta (Real.pi/k)=k := by
  have hkR : (k:ℝ)≠0 := by exact_mod_cast hk.ne'
  constructor
  · unfold xi
    field_simp
  · unfold eta
    field_simp

/-- The article's lag-one region is exactly the lattice half-plane test. -/
theorem omegaOne_iff_halfplane (q : General.Tuning) : General.Regions.OmegaOne q ↔
    ∀ ω : Frequency,0<(ω:ℝ)→xi (ω:ℝ) (tuningCurve q ω)<1 := by
  rw [General.Regions.omegaOne_iff_angle]
  constructor
  · intro h ω hω
    apply (xi_lt_one_iff ((tuningCurve q).pos ω)).mpr
    exact h (ω:ℝ) ⟨hω,ω.property.2⟩
  · intro h ω hω
    have hf : ω∈Icc 0 Real.pi := ⟨hω.1.le,hω.2⟩
    exact (xi_lt_one_iff ((tuningCurve q).pos ⟨ω,hf⟩)).mp (h ⟨ω,hf⟩ hω.1)

end polyak.Levels.Lattice
