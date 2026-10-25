import polyak.Levels.Program.Definitions
import polyak.Levels.Chart.Coefficients
import polyak.General.AngleComparison

/-! Feasibility depends only on the three actual coefficients of Xi. -/
noncomputable section
namespace polyak.Levels

theorem tuningCurve_eq_of_Xi (q p : General.Tuning) (he : ∀c,q.Xi c=p.Xi c) :
    tuningCurve q=tuningCurve p := by
  apply Curve.ext
  intro ω
  by_cases h0 : (ω:ℝ)=0
  · have hw : ω=frequencyZero:=Subtype.ext h0
    rw [hw,(tuningCurve q).at_zero,(tuningCurve p).at_zero]
  by_cases hπ : (ω:ℝ)=Real.pi
  · have hw : ω=frequencyPi:=Subtype.ext hπ
    rw [hw,(tuningCurve q).at_pi,(tuningCurve p).at_pi]
  have hi : (ω:ℝ)∈Set.Ioo (0:ℝ) Real.pi:=
    ⟨lt_of_le_of_ne ω.property.1 (Ne.symm h0),lt_of_le_of_ne ω.property.2 hπ⟩
  have hc : Real.cos (q.angle ω)/Real.sin (q.angle ω)=
      Real.cos (p.angle ω)/Real.sin (p.angle ω):=by
    rw [q.cot_angle hi,p.cot_angle hi,he]
  change q.angle ω=p.angle ω
  apply le_antisymm
  · by_contra hn
    have hh:=(General.cot_strictAnti (q.angle_mem hi) (p.angle_mem hi)).mpr (lt_of_not_ge hn)
    rw [hc] at hh
    exact lt_irrefl _ hh
  · by_contra hn
    have hh:=(General.cot_strictAnti (p.angle_mem hi) (q.angle_mem hi)).mpr (lt_of_not_ge hn)
    rw [hc] at hh
    exact lt_irrefl _ hh

theorem tuningCurve_eq_of_coefficients (q p : General.Tuning)
    (he : Chart.coefficients q=Chart.coefficients p) : tuningCurve q=tuningCurve p := by
  apply tuningCurve_eq_of_Xi
  intro c
  rw [←Chart.eval_coefficients q,he,Chart.eval_coefficients]

theorem fp_iff_of_coefficients (q p : General.Tuning)
    (he : Chart.coefficients q=Chart.coefficients p) : FP (tuningCurve q) ↔ FP (tuningCurve p) := by
  rw [tuningCurve_eq_of_coefficients q p he]

end polyak.Levels
