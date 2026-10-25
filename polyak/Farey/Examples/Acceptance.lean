import polyak.Farey.Examples.FloorCertificate
import polyak.Farey.Examples.ThirteenContracts

/-! Exact acceptance theorems for the two rational examples, with explicit
numerical premises proved in `CertifiedExamples.Rational`. -/
noncomputable section
namespace polyak.Farey.Examples
open Levels MeasureTheory

theorem thirteen_no_single_of_certificates (C:FloorCertificate thirteenXiSource)
    (hs:SmallDenominatorChecks (tuningCurve thirteenTuning)) :
    ∀ω:Levels.Frequency,¬ProgramSolution (tuningCurve thirteenTuning) nonzeroLags (Measure.dirac ω) := by
  apply no_single_harmonic_of_small_checks (tuningCurve thirteenTuning) _ hs
  intro ω _
  exact thirteen_floor_of_certificate C ω ω.property

/-- Proposition 3.13 from its floor, gap and finite-sign certificates. -/
theorem thirteen_acceptance (C:FloorCertificate thirteenXiSource)
    (hgap:GapFourChecks thirteenTuning)
    (hs:SmallDenominatorChecks (tuningCurve thirteenTuning)) (hnum:ThirteenFiniteSigns) :
    Geometry.Gap 4 thirteenTuning ∧
      (∀ω:Levels.Frequency,Real.pi/6<thirteenTuning.angle ω) ∧
      (∀ω:Levels.Frequency,¬ProgramSolution (tuningCurve thirteenTuning) nonzeroLags (Measure.dirac ω)) ∧
      RawSpectrumSolution thirteenTuning thirteenNu ∧
      ProgramSolution (tuningCurve thirteenTuning) nonzeroLags thirteenW ∧
      FanPeriodicOrbit thirteenTuning 13 2 ∧ 1≤thirteenTuning.rate := by
  have hfinite:=thirteen_from_finite_signs hnum
  exact ⟨gap_four_of_checks hgap,fun ω=>thirteen_floor_of_certificate C ω ω.property,
    thirteen_no_single_of_certificates C hs,hfinite.1,hfinite.2.1,
    thirteen_orbit_of_finite_signs hnum,hfinite.2.2⟩

theorem convergence_acceptance (hgap:GapFourChecks convergenceTuning)
    (depth:ℕ)
    (hc:LeanCert.Engine.QPoly.bernsteinCheck .strictLower convergenceSexticCode.code 0
      ⟨-1,1,by norm_num⟩ depth=true) :
    Geometry.Gap 4 convergenceTuning ∧ convergenceTuning.rate<1 :=
  ⟨gap_four_of_checks hgap,convergence_from_bernstein depth hc⟩

end polyak.Farey.Examples
