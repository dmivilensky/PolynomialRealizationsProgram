import polyak.GapEdges.Tips.Base
import polyak.GapEdges.Specialization.Opening

/-! On a first tongue edge, vanishing chi characterizes the actual tips. -/
noncomputable section
namespace polyak.GapEdges
open General Levels Set

theorem first_shift_eq_zero_of_phase (q : Tuning) {k : ℕ} (hk : 3 ≤ k)
    (hphase : q.angle (2 * Real.pi / k) = Real.pi / k) :
    FareyPlateau.Edge.shift q k (2 * Real.pi / k) = 0 := by
  have hω := Chart.boundaryAngle_strict_mem hk
  change 2 * Real.pi / (k : ℝ) ∈ Ioo 0 Real.pi at hω
  have he := q.cot_angle hω
  rw [hphase] at he
  unfold FareyPlateau.Edge.shift Geometry.cotangent
  rw [← he, sub_self]

theorem first_edge_chi_zero_iff_tip (q : Tuning) {k : ℕ} (hk : 3 ≤ k)
    (hphase : q.angle (2 * Real.pi / k) = Real.pi / k) :
    firstChi q k = 0 ↔ Tip q k := by
  have hs := first_shift_eq_zero_of_phase q hk hphase
  constructor
  · intro hchi
    have hempty := (first_dip_empty_iff q hk).mpr hchi
    rw [hs] at hempty
    have hweak : ∀ x ∈ Ioc (0 : ℝ) Real.pi, x / 2 ≤ q.angle x := by
      intro x hx
      apply le_of_not_gt
      intro hlt
      have hh : x ∈ Geometry.dipReal q 0 := by
        refine ⟨⟨hx.1.le, hx.2⟩, ?_⟩
        have he : Geometry.shiftedAngle q 0 x = q.angle x := by
          exact congrArg (fun Θ : Curve => Θ ⟨x, hx.1.le, hx.2⟩) (Geometry.shiftedCurve_zero q)
        rwa [he]
      simp only [hempty, mem_empty_iff_false] at hh
    have hω := Chart.boundaryAngle_strict_mem hk
    refine ⟨hk, Geometry.weak_contact_mem_frontier q hweak ⟨hω.1, hω.2.le⟩ ?_, hphase⟩
    change q.angle (2 * Real.pi / k) = (2 * Real.pi / k) / 2
    rw [hphase]
    ring
  · intro T
    unfold firstChi firstEdgePhase
    rw [hs]
    have hd := T.phase_deriv
    rw [T.frequency_coe] at hd
    rw [hd, sub_self]

end polyak.GapEdges
