import polyak.Levels.Geometry.Boundary
import polyak.Levels.Chart.GapPolynomial

/-! The double-root face consists of genuine relative lag-one boundary points. -/
noncomputable section
namespace polyak.Levels.Chart
open General Set

theorem double_root_boundary (q : Tuning) {a r : ℝ} (ha : 0<a)
    (hr : r∈Ioo (-1:ℝ) 1) (he : coefficients q=gapPolynomial a r r) :
    (∀ω∈Ioc (0:ℝ) Real.pi,ω/2≤q.angle ω) ∧
      q.angle (Real.arccos r)=Real.arccos r/2 ∧
      q∈frontier {p:Tuning | Regions.OmegaOne p} := by
  have hpoly (c:ℝ) : q.Xi c=1+c-a*(c-r)^2 := by
    rw [←eval_coefficients,he,gapPolynomial_eval]
    ring
  have hweak : ∀ω∈Ioc (0:ℝ) Real.pi,ω/2≤q.angle ω := by
    intro ω hω
    by_cases hp : ω=Real.pi
    · rw [hp,q.angle_pi]
      linarith [Real.pi_pos]
    · apply le_of_not_gt
      intro hn
      have hh:=(angle_lt_half_iff_Xi q ⟨hω.1,lt_of_le_of_ne hω.2 hp⟩).mp hn
      rw [hpoly] at hh
      nlinarith [mul_nonneg ha.le (sq_nonneg (Real.cos ω-r))]
  have hi : Real.arccos r∈Ioo (0:ℝ) Real.pi:=
    ⟨Real.arccos_pos.mpr hr.2,Real.arccos_lt_pi.mpr hr.1⟩
  have hcontact : q.angle (Real.arccos r)=Real.arccos r/2 := by
    apply (angle_eq_half_iff_Xi q hi).mpr
    rw [hpoly,Real.cos_arccos hr.1.le hr.2.le]
    ring
  exact ⟨hweak,hcontact,Geometry.weak_contact_mem_frontier q hweak ⟨hi.1,hi.2.le⟩ hcontact⟩

end polyak.Levels.Chart
