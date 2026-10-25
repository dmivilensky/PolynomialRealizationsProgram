import polyak.CertifiedExamples.Exact313.Tangencies
import polyak.CertifiedExamples.Exact313.Numerical
import polyak.ModeLocking.TwoLag.ExactThreshold
import polyak.ModeLocking.Plateaus.Exact

/-! The concrete 3/13 example satisfies all primary E1–E4 hypotheses.
Every resulting boundary, threshold and open-plateau conclusion concerns
an actual admissible tuning and the original full measure program. -/
noncomputable section
namespace polyak.CertifiedExamples.Exact313
open General Levels ModeLocking.TwoLag Set MeasureTheory

def exactData : ExactData qStar 0 4 13 where
  K_ge := by norm_num
  L_ge := by norm_num
  u := atoms
  interior := atoms_interior
  a := 1/(1+rStar)
  b := rStar/(1+rStar)
  a_pos := one_div_pos.mpr (by linarith [scalarRoot_positive])
  b_pos := div_pos scalarRoot_positive (by linarith [scalarRoot_positive])
  normalized := by field_simp [show 1+rStar≠0 by linarith [scalarRoot_positive]]
  nonpos := lagTangencies.nonpos
  zero_set := by
    intro x hx
    rw [lagTangencies.zero_set x ⟨hx.1.le,hx.2.le⟩]
    constructor
    · intro h
      rcases h with h|⟨i,hi⟩
      · exact False.elim (hx.1.ne' h)
      · fin_cases i
        · exact Or.inl hi
        · exact Or.inr hi
    · intro h
      right
      rcases h with h|h
      · exact ⟨0,h⟩
      · exact ⟨1,h⟩
  endpoint_curv := lagTangencies.endpoint_curv
  curv := lagTangencies.support_curv
  sign₁ := by rw [Geometry.shiftedCurve_zero];exact lag_signs_first.1
  sign₂ := by rw [Geometry.shiftedCurve_zero];exact lag_signs_second.2
  opposite₁ := by rw [Geometry.shiftedCurve_zero];exact lag_signs_first.2
  opposite₂ := by rw [Geometry.shiftedCurve_zero];exact lag_signs_second.1
  grid := atoms_grid
  inactive := by
    intro n hn0 hn13 hn1 hn9
    rw [Geometry.shiftedCurve_zero]
    exact inactive_strict n hn0 hn13 hn1 (by norm_num at hn9;exact hn9)
  minimizer := by rw [Geometry.shiftedCurve_zero];exact minimizer_strict
  determinant := sine_determinant_nonzero

theorem qStar_regular : ModeLocking.RegularPoint qStar 0 13 := exactData.regular

theorem thresholds_zero :
    Threshold.sigma qStar=0 ∧ Threshold.sigmaPeriodic qStar 13=0 ∧
      Threshold.sigmaOn qStar (pairLags 4)=0 :=
  ⟨exactData.sigma_eq,exactData.sigmaPeriodic_eq,exactData.sigmaPair_eq⟩

theorem qStar_gap : Geometry.Gap 4 qStar := exactData.gap_of_first_contact_window first_in_window

theorem qStar_boundary : qStar∈ModeLocking.BoundaryInGap 4 :=
  exactData.boundary_of_first_contact_window first_in_window

theorem open_analytic_plateau :
    exactData.boundaryPoint.val∈ModeLocking.Plateaus.plateau exactData.boundaryPoint.val ∧
      IsOpen (ModeLocking.Plateaus.projectedPlateau exactData.boundaryPoint.val) ∧
      IsConnected (ModeLocking.Plateaus.projectedPlateau exactData.boundaryPoint.val) ∧
      AnalyticOnNhd ℝ ModeLocking.Plateaus.ambientKappaBoundary
        (ModeLocking.Plateaus.projectedPlateau exactData.boundaryPoint.val) :=
  ⟨exactData.lies_on_open_plateau.1,exactData.plateau_analytic_boundary⟩

theorem unique_anchor {w : Measure Frequency}
    (hw : ProgramSolution (tuningCurve qStar) nonzeroLags w) (ω : Frequency) :
    Farey.Anchor qStar w ω ↔ ω=atoms 0 :=
  exactData.plateau_unique_anchor second_below_window
    exactData.lies_on_open_plateau.1 qStar_gap hw ω

end polyak.CertifiedExamples.Exact313
