import polyak.ModeLocking.Regular.ExactRelaxations

/-! Every superset of the regular lag set is exact. Even inserting the
identically zero lag requires no exception in this quantifier. -/
noncomputable section
namespace polyak.ModeLocking
open General Levels Filter Set
open scoped Topology

theorem program_erase_zero (Θ : Curve) (N : Set ℤ) (w : MeasureTheory.Measure Frequency) :
    ProgramSolution Θ N w ↔ ProgramSolution Θ (N ∩ nonzeroLags) w := by
  refine ⟨fun hw => hw.relax inter_subset_left, ?_⟩
  intro hw
  refine ⟨hw.1, hw.2.1, hw.2.2.1, ?_⟩
  intro n hn
  by_cases hz : n = 0
  · simp only [hz, Curve.lag_zero, MeasureTheory.integral_zero, le_refl]
  · exact hw.2.2.2 n ⟨hn, hz⟩

theorem fpOn_erase_zero (Θ : Curve) (N : Set ℤ) : FPOn Θ N ↔ FPOn Θ (N ∩ nonzeroLags) :=
  exists_congr fun w => program_erase_zero Θ N w

theorem sigmaOn_erase_zero (q : Tuning) (N : Set ℤ) :
    Threshold.sigmaOn q N = Threshold.sigmaOn q (N ∩ nonzeroLags) := by
  unfold Threshold.sigmaOn
  congr 1
  ext s
  exact fpOn_erase_zero (Geometry.shiftedCurve q s) N

namespace RegularData
variable {q : Tuning} {s : ℝ} {L : ℕ} (D : RegularData q s L)

theorem sigmaOn_eq_all {N' : Set ℤ} (hN : (D.lags : Set ℤ) ⊆ N') : Threshold.sigmaOn q N' = s := by
  rw [sigmaOn_erase_zero]
  exact D.sigmaOn_eq (fun n hn => ⟨hN hn, D.lags_nonzero n hn⟩) inter_subset_right

theorem exact_relaxation_all {N' : Set ℤ} (hN : (D.lags : Set ℤ) ⊆ N')
    (w : MeasureTheory.Measure Frequency) : ProgramSolution (Geometry.shiftedCurve q s) N' w ↔
      ProgramSolution (Geometry.shiftedCurve q s) nonzeroLags w := by
  have hsub : (D.lags : Set ℤ) ⊆ N' ∩ nonzeroLags :=
    fun n hn => ⟨hN hn, D.lags_nonzero n hn⟩
  exact (program_erase_zero (Geometry.shiftedCurve q s) N' w).trans
    (D.exact_relaxation hsub inter_subset_right w)

theorem all_supersets_exact_near : ∀ᶠ q' in 𝓝 q, ∀ N' : Set ℤ, (D.lags : Set ℤ) ⊆ N' →
    Threshold.sigmaOn q' N' = Threshold.sigma q' ∧
      ∀ w : MeasureTheory.Measure Frequency,
        ProgramSolution (Geometry.shiftedCurve q' (Threshold.sigma q')) N' w ↔
          ProgramSolution (Geometry.shiftedCurve q' (Threshold.sigma q')) nonzeroLags w := by
  filter_upwards [D.regular_persistence] with q' hq' N' hN
  obtain ⟨D', _, _, hlag⟩ := hq'
  have hN' : (D'.lags : Set ℤ) ⊆ N' := by rw [hlag]; exact hN
  exact ⟨D'.sigmaOn_eq_all hN', fun w => D'.exact_relaxation_all hN' w⟩

end RegularData
end polyak.ModeLocking
