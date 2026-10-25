import polyak.CertifiedExamples.Plateaus.Regular
import polyak.CertifiedExamples.Plateaus.Anchors
import polyak.CertifiedExamples.Plateaus.Boundary
import polyak.Levels.Realization.ExactThreshold

/-! Conclusions for the two mixed-spectrum plateaus of Theorem 3.17. All numerical
premises enter through the independently checked primary regular data. -/
noncomputable section
namespace polyak.CertifiedExamples.Plateaus
open General Levels ModeLocking ModeLocking.Plateaus Set MeasureTheory

theorem row18_thresholds : Threshold.sigma tuning18=0 ∧
    Threshold.sigmaPeriodic tuning18 18=0 :=
  ⟨row18_regularData.sigma_eq,row18_regularData.sigmaPeriodic_eq⟩

theorem row21_thresholds : Threshold.sigma tuning21=0 ∧
    Threshold.sigmaPeriodic tuning21 21=0 :=
  ⟨row21_regularData.sigma_eq,row21_regularData.sigmaPeriodic_eq⟩

theorem row18_finite_threshold : Threshold.sigmaOn tuning18 (lags18:Set ℤ)=0 :=
  row18_regularData.sigmaOn_eq (fun _ h=>h) (fun n hn=>row18_regularData.lags_nonzero n hn)

theorem row21_finite_threshold : Threshold.sigmaOn tuning21 (lags21:Set ℤ)=0 :=
  row21_regularData.sigmaOn_eq (fun _ h=>h) (fun n hn=>row21_regularData.lags_nonzero n hn)

theorem row18_rate_ge_one : 1≤tuning18.rate := by
  by_contra hn
  have h := (rate_lt_one_iff_infeasible tuning18).mp (lt_of_not_ge hn)
  apply h
  exact ⟨row18_regularData.measure,by
    simpa only [Geometry.shiftedCurve_zero] using row18_regularData.primal_feasible⟩

theorem row21_rate_ge_one : 1≤tuning21.rate := by
  by_contra hn
  have h := (rate_lt_one_iff_infeasible tuning21).mp (lt_of_not_ge hn)
  apply h
  exact ⟨row21_regularData.measure,by
    simpa only [Geometry.shiftedCurve_zero] using row21_regularData.primal_feasible⟩

theorem row18_boundary_coordinate :
    (Global.Threshold.kappaBoundary (Global.Threshold.parameters tuning18)).val=
      (tuning18.kappa:EReal) := regular_kappa_boundary row18_regularData

theorem row21_boundary_coordinate :
    (Global.Threshold.kappaBoundary (Global.Threshold.parameters tuning21)).val=
      (tuning21.kappa:EReal) := regular_kappa_boundary row21_regularData

theorem row18_periods (k:ℕ) : PeriodicFP (tuningCurve tuning18) k ↔18∣k := by
  simpa only [Geometry.shiftedCurve_zero] using row18_regularData.periodic_iff_dvd k

theorem row21_periods (k:ℕ) : PeriodicFP (tuningCurve tuning21) k ↔21∣k := by
  simpa only [Geometry.shiftedCurve_zero] using row21_regularData.periodic_iff_dvd k

theorem row18_minimal_period : IsLeast {k:ℕ | 0<k ∧ PeriodicFP (tuningCurve tuning18) k} 18 := by
  refine ⟨⟨by norm_num,(row18_periods 18).mpr (dvd_refl _)⟩,?_⟩
  intro k hk
  exact Nat.le_of_dvd hk.1 ((row18_periods k).mp hk.2)

theorem row18_no_fan_period (p:ℕ) : ¬PeriodicFP (tuningCurve tuning18) (p*4+1) := by
  rw [row18_periods]
  intro h
  have h2 : 2∣p*4+1 := dvd_trans (by norm_num : 2∣18) h
  omega

theorem row21_no_two_atom_optimizer (weights:Fin 2→NNReal) (sites:Fin 2→Frequency) :
    ¬ProgramSolution (tuningCurve tuning21) nonzeroLags (atomicMeasure weights sites) := by
  simpa only [Geometry.shiftedCurve_zero] using
    regular_no_two_atom row21_regularData (by decide) weights sites

theorem row18_extremals (w:Measure Frequency) :
    ProgramSolution (tuningCurve tuning18) nonzeroLags w ↔
      ∃c a:NNReal,0<c ∧
        w=(c:ENNReal) • row18_regularData.measure+(a:ENNReal) • Measure.dirac frequencyZero ∧
        (a:ℝ)≤(c:ℝ)*∫ω,(tuningCurve tuning18).minimizer ω ∂row18_regularData.measure := by
  simpa only [Geometry.shiftedCurve_zero] using row18_regularData.extremal_iff (N':=nonzeroLags)
    (fun n hn=>row18_regularData.lags_nonzero n hn) (fun _ h=>h) w

theorem row21_extremals (w:Measure Frequency) :
    ProgramSolution (tuningCurve tuning21) nonzeroLags w ↔
      ∃c a:NNReal,0<c ∧
        w=(c:ENNReal) • row21_regularData.measure+(a:ENNReal) • Measure.dirac frequencyZero ∧
        (a:ℝ)≤(c:ℝ)*∫ω,(tuningCurve tuning21).minimizer ω ∂row21_regularData.measure := by
  simpa only [Geometry.shiftedCurve_zero] using row21_regularData.extremal_iff (N':=nonzeroLags)
    (fun n hn=>row21_regularData.lags_nonzero n hn) (fun _ h=>h) w

def boundary18 : regularBoundary := regularBoundaryPoint row18_regularData
def boundary21 : regularBoundary := regularBoundaryPoint row21_regularData

theorem row18_open_plateau : boundary18.val∈plateau boundary18.val ∧
    IsOpen (plateau boundary18.val) ∧ IsConnected (plateau boundary18.val) :=
  regular_open_plateau row18_regularData

theorem row21_open_plateau : boundary21.val∈plateau boundary21.val ∧
    IsOpen (plateau boundary21.val) ∧ IsConnected (plateau boundary21.val) :=
  regular_open_plateau row21_regularData

theorem row18_analytic_plateau : IsOpen (projectedPlateau boundary18.val) ∧
    IsConnected (projectedPlateau boundary18.val) ∧
    AnalyticOnNhd ℝ ambientKappaBoundary (projectedPlateau boundary18.val) :=
  regular_analytic_plateau row18_regularData

theorem row21_analytic_plateau : IsOpen (projectedPlateau boundary21.val) ∧
    IsConnected (projectedPlateau boundary21.val) ∧
    AnalyticOnNhd ℝ ambientKappaBoundary (projectedPlateau boundary21.val) :=
  regular_analytic_plateau row21_regularData

theorem row18_unique_anchor {r:regularBoundary} (hr:r.val∈plateau boundary18.val)
    (hgap:Geometry.Gap 4 r.val.val) {w:Measure Frequency}
    (hw:ProgramSolution (tuningCurve r.val.val) nonzeroLags w) :
    ∀ω:Frequency,Farey.Anchor r.val.val w ω ↔ω=atoms18 1 :=
  regular_plateau_unique_anchor row18_regularData row18_only_window_atom hr hgap hw

theorem row21_unique_anchor {r:regularBoundary} (hr:r.val∈plateau boundary21.val)
    (hgap:Geometry.Gap 4 r.val.val) {w:Measure Frequency}
    (hw:ProgramSolution (tuningCurve r.val.val) nonzeroLags w) :
    ∀ω:Frequency,Farey.Anchor r.val.val w ω ↔ω=atoms21 2 :=
  regular_plateau_unique_anchor row21_regularData row21_only_window_atom hr hgap hw

end polyak.CertifiedExamples.Plateaus
