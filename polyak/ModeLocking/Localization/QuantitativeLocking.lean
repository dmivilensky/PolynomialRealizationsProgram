import polyak.ModeLocking.Localization.GridDistance

/-! Sharp quantitative locking of every competing period, in the explicit
epsilon-delta form of the article's asymptotic statement. -/
noncomputable section
namespace polyak.ModeLocking.Localization
open Levels MeasureTheory Set
variable {q : General.Tuning} {t : ℝ} {L : ℕ}

theorem quantitative_locking_periods (D : RegularData q t L) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ M (hM : 3 ≤ M),
      (∀ i, D.atoms i ∉ periodicGrid M) → gridSupportDistance D M hM < δ →
      (minimalLockingCoefficient D-ε)*(gridSupportDistance D M hM)^2 ≤
        Threshold.sigmaPeriodic q M-t := by
  by_cases hεc : ε < minimalLockingCoefficient D
  · obtain ⟨δ,hδ,hsharp⟩ := regular_sharp_potential_penalty D ε hε hεc
    refine ⟨δ,hδ,?_⟩
    intro M hM hdisj hdist
    obtain ⟨w,hw,hcar⟩ := Threshold.sigmaPeriodic_feasible q hM
    have hsupport : w.support ⊆ periodicGrid M :=
      w.support_subset_of_isClosed (periodicGrid_finite (by omega : 0<M)).isClosed hcar
    apply support_potential_penalty D (Threshold.sigmaPeriodic q M)
      ((minimalLockingCoefficient D-ε)*(gridSupportDistance D M hM)^2) hw
    intro ω hω hωint
    have hg := hsupport hω
    have hh := hsharp (gridSupportDistance D M hM) (gridSupportDistance_pos D M hM hdisj)
      hdist (ω:ℝ) hωint (gridSupportDistance_le_infDist D M hM hg)
    rwa [extendedPotential_actual D ω] at hh
  · refine ⟨1,by norm_num,?_⟩
    intro M hM _hdisj _hdist
    have hg : 0 ≤ Threshold.sigmaPeriodic q M-t := by
      rw [← D.sigma_eq]
      exact sub_nonneg.mpr (Threshold.sigma_le_sigmaPeriodic q hM)
    exact (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (le_of_not_gt hεc)) (sq_nonneg _)).trans hg

theorem quantitative_locking_relative (D : RegularData q t L) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ M (hM : 3 ≤ M),
      (∀ i, D.atoms i ∉ periodicGrid M) → gridSupportDistance D M hM < δ →
      minimalLockingCoefficient D*(gridSupportDistance D M hM)^2*(1-ε) ≤
        Threshold.sigmaPeriodic q M-t := by
  obtain ⟨δ,hδ,hpenalty⟩ := quantitative_locking_periods D
    (minimalLockingCoefficient D*ε) (mul_pos (minimalLockingCoefficient_pos D) hε)
  refine ⟨δ,hδ,?_⟩
  intro M hM hdisj hdist
  have hh := hpenalty M hM hdisj hdist
  convert hh using 1
  ring

end polyak.ModeLocking.Localization
