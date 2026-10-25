import polyak.ModeLocking.Regular.Persistence
import polyak.ModeLocking.Regular.Uniqueness
import polyak.Levels.Realization.ExactThreshold

/-! The finite regular certificate decides the full program locally. Every
superset of its lags is exact, including its arbitrary finite-measure solutions. -/
noncomputable section
namespace polyak.ModeLocking.RegularData
open General Levels Filter Set
open scoped Topology
variable {q : Tuning} {s : ℝ} {L : ℕ} (D : RegularData q s L)
include D

theorem convergence_iff_shift_pos : q.rate < 1 ↔ 0 < s := by
  rw [rate_lt_one_iff_infeasible, Threshold.fp_iff_sigma_nonpos, D.sigma_eq, not_le]

theorem finite_feasible_iff : FPOn (tuningCurve q) (D.lags : Set ℤ) ↔ s ≤ 0 := by
  rw [← Geometry.shiftedCurve_zero q]
  rw [Threshold.shifted_feasible_iff q (D.lags : Set ℤ) (fun n hn => D.lags_nonzero n hn),
    D.sigmaOn_eq (Subset.refl _) (fun n hn => D.lags_nonzero n hn)]

theorem periodic_feasible_iff : PeriodicFP (tuningCurve q) L ↔ s ≤ 0 := by
  rw [← Geometry.shiftedCurve_zero q, Threshold.shifted_periodic_iff q D.period_ge, D.sigmaPeriodic_eq]

theorem convergence_iff_finite_infeasible : q.rate < 1 ↔ ¬ FPOn (tuningCurve q) (D.lags : Set ℤ) := by
  rw [D.convergence_iff_shift_pos, D.finite_feasible_iff, not_le]

theorem convergence_iff_periodic_infeasible : q.rate < 1 ↔ ¬ PeriodicFP (tuningCurve q) L := by
  rw [D.convergence_iff_shift_pos, D.periodic_feasible_iff, not_le]

theorem exact_relaxations_near : ∀ᶠ q' in 𝓝 q, ∀ N' : Set ℤ,
    (D.lags : Set ℤ) ⊆ N' → N' ⊆ nonzeroLags →
      Threshold.sigmaOn q' N' = Threshold.sigma q' ∧
      Threshold.sigmaPeriodic q' L = Threshold.sigma q' ∧
      ∀ w : MeasureTheory.Measure Frequency,
        ProgramSolution (Geometry.shiftedCurve q' (Threshold.sigma q')) N' w ↔
          ProgramSolution (Geometry.shiftedCurve q' (Threshold.sigma q')) nonzeroLags w := by
  filter_upwards [D.regular_persistence] with q' hq' N' hN hN'
  obtain ⟨D', _, _, hlag⟩ := hq'
  have hN'' : (D'.lags : Set ℤ) ⊆ N' := by rw [hlag]; exact hN
  refine ⟨D'.sigmaOn_eq hN'' hN', D'.sigmaPeriodic_eq, fun w => D'.exact_relaxation hN'' hN' w⟩

theorem local_convergence_criterion : ∀ᶠ q' in 𝓝 q,
    (q'.rate < 1 ↔ ¬ FPOn (tuningCurve q') (D.lags : Set ℤ)) ∧
    (q'.rate < 1 ↔ ¬ PeriodicFP (tuningCurve q') L) ∧
    (q'.rate < 1 ↔ 0 < Threshold.sigma q') := by
  filter_upwards [D.regular_persistence] with q' hq'
  obtain ⟨D', _, _, hlag⟩ := hq'
  refine ⟨?_, D'.convergence_iff_periodic_infeasible, D'.convergence_iff_shift_pos⟩
  simpa only [hlag] using D'.convergence_iff_finite_infeasible

end polyak.ModeLocking.RegularData
