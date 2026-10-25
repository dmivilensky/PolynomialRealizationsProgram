import polyak.Global.Threshold.PeriodicBoundary
import polyak.Levels.Realization.ThresholdSets

/-! On the actual divergence boundary the attained threshold program
is exactly the original program, with the same measures as solutions. -/
noncomputable section
namespace polyak.Global.Threshold
open General Levels Set MeasureTheory

theorem sigma_eq_zero_on_frontier_of_continuous (hσ : Continuous sigma)
    {q : Tuning} (hq : q∈frontier Regions.divergenceSet) : sigma q=0 := by
  have he : Regions.divergenceSet={p : Tuning | sigma p≤0} := by
    ext p
    exact divergenceSet_iff_sigma_nonpos p
  rw [he] at hq
  have hc : IsClosed {p : Tuning | sigma p≤0} := isClosed_le hσ continuous_const
  have hle : sigma q≤0 := hc.frontier_subset hq
  apply le_antisymm hle
  by_contra hn
  have hlt : sigma q<0 := lt_of_not_ge hn
  have ho : IsOpen {p : Tuning | sigma p<0} := isOpen_lt hσ continuous_const
  have hi : {p : Tuning | sigma p<0}⊆interior {p : Tuning | sigma p≤0} :=
    ho.subset_interior_iff.mpr (fun p (hp : sigma p<0)=>hp.le)
  exact hq.2 (hi hlt)

def thresholdExtremals (q : Tuning) : Set (Measure Frequency) :=
  {w | ProgramSolution (Geometry.shiftedCurve q (sigma q)) nonzeroLags w}

theorem thresholdExtremals_nonempty (q : Tuning) : (thresholdExtremals q).Nonempty :=
  Levels.Threshold.sigma_feasible q

theorem thresholdExtremals_eq_of_sigma_zero (q : Tuning) (hσ : sigma q=0) :
    thresholdExtremals q={w | ProgramSolution (tuningCurve q) nonzeroLags w} := by
  simp only [thresholdExtremals,hσ,Geometry.shiftedCurve_zero]

theorem boundary_thresholdExtremals_eq_of_continuous (hσ : Continuous sigma)
    {q : Tuning} (hq : q∈frontier Regions.divergenceSet) :
    thresholdExtremals q={w | ProgramSolution (tuningCurve q) nonzeroLags w} :=
  thresholdExtremals_eq_of_sigma_zero q (sigma_eq_zero_on_frontier_of_continuous hσ hq)

end polyak.Global.Threshold
