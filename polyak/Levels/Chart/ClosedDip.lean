import polyak.Levels.Chart.AngleGap

/-! The full closed dip is the exact interval between the two arccosine roots. -/
noncomputable section
namespace polyak.Levels.Chart
open General Set

theorem closedDip_gapPolynomial_iff (q : Tuning) {a r₁ r₂ : ℝ}
    (ha : 0<a) (hl : -1<r₁) (hr : r₁≤r₂) (hu : r₂<1)
    (he : coefficients q=gapPolynomial a r₁ r₂) (ω : Frequency) :
    ω∈Geometry.closedDip (tuningCurve q) ↔ r₁≤Real.cos (ω:ℝ) ∧ Real.cos (ω:ℝ)≤r₂ := by
  have hpoly : q.Xi (Real.cos (ω:ℝ))=(gapPolynomial a r₁ r₂).eval (Real.cos (ω:ℝ)) := by
    rw [←eval_coefficients,he]
  by_cases hω : (ω:ℝ)∈Ioo (0:ℝ) Real.pi
  · change q.angle (ω:ℝ)≤(ω:ℝ)/2 ↔ _
    rw [angle_le_half_iff_Xi q ⟨hω.1,hω.2.le⟩,hpoly,gapPolynomial_closed_dip_iff ha hr]
  · have hbad : (ω:ℝ)=0 ∨ (ω:ℝ)=Real.pi := by
      have hw := ω.property
      simp only [mem_Ioo,not_and_or,not_lt] at hω
      rcases hω with h|h
      · left; linarith [hw.1]
      · right; linarith [hw.2]
    rcases hbad with h0|hπ
    · have hfreq : ω=frequencyZero := Subtype.ext h0
      rw [hfreq]
      change q.angle 0≤0/2 ↔ _
      rw [q.angle_zero]
      simp only [frequencyZero,Real.cos_zero]
      constructor <;> intro h <;> linarith [Real.pi_pos]
    · have hfreq : ω=frequencyPi := Subtype.ext hπ
      rw [hfreq]
      change q.angle Real.pi≤Real.pi/2 ↔ _
      rw [q.angle_pi]
      simp only [frequencyPi,Real.cos_pi]
      constructor <;> intro h <;> linarith [Real.pi_pos]

theorem closedDip_interval (q : Tuning) {a r₁ r₂ : ℝ}
    (ha : 0<a) (hl : -1<r₁) (hr : r₁≤r₂) (hu : r₂<1)
    (he : coefficients q=gapPolynomial a r₁ r₂) :
    Geometry.closedDip (tuningCurve q)=
      {ω : Frequency | Real.arccos r₂≤(ω:ℝ) ∧ (ω:ℝ)≤Real.arccos r₁} := by
  ext ω
  rw [closedDip_gapPolynomial_iff q ha hl hr hu he]
  have h₁ := Real.strictAntiOn_cos.le_iff_ge
    (show Real.arccos r₁∈Icc (0:ℝ) Real.pi from ⟨Real.arccos_nonneg _,Real.arccos_le_pi _⟩)
    ω.property
  have h₂ := Real.strictAntiOn_cos.le_iff_ge ω.property
    (show Real.arccos r₂∈Icc (0:ℝ) Real.pi from ⟨Real.arccos_nonneg _,Real.arccos_le_pi _⟩)
  rw [Real.cos_arccos hl.le (hr.trans hu.le)] at h₁
  rw [Real.cos_arccos (hl.le.trans hr) hu.le] at h₂
  exact (and_congr h₁ h₂).trans and_comm

end polyak.Levels.Chart
