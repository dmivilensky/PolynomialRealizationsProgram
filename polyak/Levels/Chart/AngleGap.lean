import polyak.Levels.Chart.GapPolynomial
import polyak.Levels.Geometry.Gap
import polyak.General.AngleComparison

/-! Exact comparisons between the source dip and the gap polynomial. -/
noncomputable section
namespace polyak.Levels.Chart
open General Set

theorem angle_lt_half_iff_Xi (q : Tuning) {ω : ℝ} (hω : ω∈Ioo (0:ℝ) Real.pi) :
    q.angle ω<ω/2 ↔ 1+Real.cos ω<q.Xi (Real.cos ω) := by
  have hh : ω/2∈Ioo (0:ℝ) Real.pi := ⟨by linarith [hω.1],by linarith [hω.2,Real.pi_pos]⟩
  rw [← cot_strictAnti hh (q.angle_mem hω),cot_half hω,q.cot_angle hω,
    div_lt_div_iff_of_pos_right (Real.sin_pos_of_pos_of_lt_pi hω.1 hω.2)]

theorem angle_le_half_iff_Xi (q : Tuning) {ω : ℝ} (hω : ω∈Ioc (0:ℝ) Real.pi) :
    q.angle ω≤ω/2 ↔ 1+Real.cos ω≤q.Xi (Real.cos ω) := by
  have he := not_congr (q.angle_gt_half_iff hω)
  simp only [not_lt] at he
  rw [he,q.L_eq_Xi]
  have hp : 0<(q.y-q.x)*(1-q.beta) :=
    mul_pos (sub_pos.mpr q.x_lt_y) (sub_pos.mpr q.beta_lt_one)
  constructor
  · intro h
    have hh := nonpos_of_mul_nonpos_right h hp
    linarith
  · intro h
    exact mul_nonpos_of_nonneg_of_nonpos hp.le (by linarith)

theorem angle_gt_half_iff_Xi (q : Tuning) {ω : ℝ} (hω : ω∈Ioc (0:ℝ) Real.pi) :
    ω/2<q.angle ω ↔ q.Xi (Real.cos ω)<1+Real.cos ω := by
  have he := not_congr (angle_le_half_iff_Xi q hω)
  simpa only [not_le] using he

theorem angle_eq_half_iff_Xi (q : Tuning) {ω : ℝ} (hω : ω∈Ioo (0:ℝ) Real.pi) :
    q.angle ω=ω/2 ↔ q.Xi (Real.cos ω)=1+Real.cos ω := by
  constructor
  · intro he
    apply le_antisymm
    · by_contra hh
      have ht := (angle_lt_half_iff_Xi q hω).mpr (lt_of_not_ge hh)
      rw [he] at ht
      exact False.elim (lt_irrefl _ ht)
    · exact (angle_le_half_iff_Xi q ⟨hω.1,hω.2.le⟩).mp he.le
  · intro he
    have hl := (angle_le_half_iff_Xi q ⟨hω.1,hω.2.le⟩).mpr he.ge
    apply le_antisymm hl
    by_contra hh
    have ht := (angle_lt_half_iff_Xi q hω).mp (lt_of_not_ge hh)
    linarith

theorem dip_gapPolynomial_iff (q : Tuning) {a r₁ r₂ : ℝ}
    (ha : 0<a) (hl : -1<r₁) (hr : r₁<r₂) (hu : r₂<1)
    (he : coefficients q=gapPolynomial a r₁ r₂) (ω : Frequency) :
    ω∈Geometry.dip (tuningCurve q) ↔ r₁<Real.cos (ω:ℝ) ∧ Real.cos (ω:ℝ)<r₂ := by
  have hpoly : q.Xi (Real.cos (ω:ℝ))=(gapPolynomial a r₁ r₂).eval (Real.cos (ω:ℝ)) := by
    rw [← eval_coefficients,he]
  by_cases hω : (ω:ℝ)∈Ioo (0:ℝ) Real.pi
  · change q.angle (ω:ℝ)<(ω:ℝ)/2 ↔ _
    rw [angle_lt_half_iff_Xi q hω,hpoly,gapPolynomial_dip_iff ha hr]
  · have hbad : (ω:ℝ)=0 ∨ (ω:ℝ)=Real.pi := by
      have hw := ω.property
      simp only [mem_Ioo,not_and_or,not_lt] at hω
      rcases hω with h|h
      · left; linarith [hw.1]
      · right; linarith [hw.2]
    rcases hbad with h0|hπ
    · have hfreq : ω=frequencyZero := Subtype.ext h0
      rw [hfreq]
      change q.angle 0<0/2 ↔ _
      rw [q.angle_zero]
      simp only [frequencyZero,Real.cos_zero]
      constructor <;> intro h <;> linarith [Real.pi_pos]
    · have hfreq : ω=frequencyPi := Subtype.ext hπ
      rw [hfreq]
      change q.angle Real.pi<Real.pi/2 ↔ _
      rw [q.angle_pi]
      simp only [frequencyPi,Real.cos_pi]
      constructor <;> intro h <;> linarith [Real.pi_pos]

end polyak.Levels.Chart
