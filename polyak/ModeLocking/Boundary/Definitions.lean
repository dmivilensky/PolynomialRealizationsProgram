import polyak.Global.Threshold.GlobalStructure
import polyak.Global.Symbols.Threshold
import polyak.Farey.Geometry.Localization

/-! The actual boundary in a gap, with all finite-measure extremals. -/
noncomputable section
namespace polyak.ModeLocking
open General Levels Set Filter MeasureTheory
open scoped Topology

def BoundaryInGap (K:ℕ) : Set Tuning:=frontier Regions.divergenceSet∩{q|Geometry.Gap K q}
def PeriodicBoundary (q:Tuning) : Prop:=∃L:ℕ,3≤L ∧ Threshold.sigmaPeriodic q L=0
def Extremal (q:Tuning) (w:Measure Frequency) : Prop:=
  ProgramSolution (Geometry.shiftedCurve q (Threshold.sigma q)) nonzeroLags w

theorem boundary_sigma_zero {K:ℕ} {q:Tuning} (hq:q∈BoundaryInGap K) : Threshold.sigma q=0:=
  Global.Threshold.sigma_eq_zero_on_frontier hq.1

theorem boundary_extremal_iff {K:ℕ} {q:Tuning} (hq:q∈BoundaryInGap K) (w:Measure Frequency) :
    Extremal q w ↔ ProgramSolution (tuningCurve q) nonzeroLags w := by
  simp only [Extremal,boundary_sigma_zero hq,Geometry.shiftedCurve_zero]

theorem boundary_extremals_nonempty {K:ℕ} {q:Tuning} (hq:q∈BoundaryInGap K) :
    ∃w:Measure Frequency,ProgramSolution (tuningCurve q) nonzeroLags w := by
  have h:=Threshold.sigma_feasible q
  rw [boundary_sigma_zero hq,Geometry.shiftedCurve_zero] at h
  exact h

theorem boundary_limit_symbol {K:ℕ} {q:Tuning} (hq:q∈BoundaryInGap K) :
    Nonempty (Global.Symbols.LimitSymbol (tuningCurve q) nonzeroLags) := by
  simpa only [boundary_sigma_zero hq,Geometry.shiftedCurve_zero] using Global.Symbols.limit_symbol q

theorem boundary_closedDip {K:ℕ} {q:Tuning} (hq:q∈BoundaryInGap K) :
    ∀ω∈Geometry.closedDip (tuningCurve q),Geometry.InWindow K ω :=
  Farey.gap_closedDip_window hq.2

theorem boundary_periodic_iff {K:ℕ} {q:Tuning} (hq:q∈BoundaryInGap K) :
    PeriodicBoundary q ↔ ∃L:ℕ,3≤L ∧ PeriodicFP (tuningCurve q) L := by
  constructor
  · rintro ⟨L,hL,he⟩
    refine ⟨L,hL,?_⟩
    have h:=Threshold.sigmaPeriodic_feasible q hL
    simpa only [he,Geometry.shiftedCurve_zero] using h
  · rintro ⟨L,hL,hp⟩
    refine ⟨L,hL,le_antisymm ?_ ?_⟩
    · exact (Threshold.shifted_periodic_iff q hL 0).mp (by
        simpa only [Geometry.shiftedCurve_zero] using hp)
    · simpa only [boundary_sigma_zero hq] using Threshold.sigma_le_sigmaPeriodic q hL

theorem boundary_periodic_anchor {K L:ℕ} {q:Tuning} (hq:q∈BoundaryInGap K) (hL:0<L)
    {w:Measure Frequency} (hw:Extremal q w) (hcar:∀ᵐω∂w,ω∈periodicGrid L) :
    ∃(ω:Frequency)(j k:ℕ),Farey.Anchor q w ω ∧ 1≤j ∧ 2*j<k ∧ j.Coprime k ∧ k∣L ∧
      (ω:ℝ)=2*Real.pi*j/k ∧ (1/((K:ℝ)+1)<(j:ℝ)/k ∧ (j:ℝ)/k<1/(K:ℝ)) ∧
      2*K+1≤k ∧ q.angle ω≤Real.pi*j/k ∧
      (¬ProgramSolution (tuningCurve q) nonzeroLags (Measure.dirac ω)→Real.pi/k<q.angle ω) :=
  Farey.farey_localization hq.2 hL ((boundary_extremal_iff hq w).mp hw) hcar

end polyak.ModeLocking
