import polyak.Levels.Realization.ExactThreshold
import polyak.Levels.Program.Grid
import polyak.Levels.Threshold.ShiftThreshold
import polyak.General.Regions.SourceSets

/-! The article's divergence set D is the actual rate threshold, with its
full-program and attained-shift descriptions. -/
noncomputable section
namespace polyak.Levels

theorem one_le_rate_iff_fp (q : General.Tuning) : 1≤q.rate ↔ FP (tuningCurve q) := by
  constructor
  · intro h
    by_contra hn
    exact (not_lt_of_ge h) ((rate_lt_one_iff_infeasible q).mpr hn)
  · exact fp_one_le_rate q

theorem divergenceSet_iff_fp (q : General.Tuning) :
    q∈General.Regions.divergenceSet ↔ FP (tuningCurve q):=one_le_rate_iff_fp q

theorem divergenceSet_iff_sigma_nonpos (q : General.Tuning) :
    q∈General.Regions.divergenceSet ↔ Threshold.sigma q≤0 := by
  rw [divergenceSet_iff_fp,Threshold.fp_iff_sigma_nonpos]

theorem periodicFP_diverges (q : General.Tuning) {k : ℕ}
    (h : PeriodicFP (tuningCurve q) k) : q∈General.Regions.divergenceSet :=
  fp_one_le_rate q h.fp

end polyak.Levels
