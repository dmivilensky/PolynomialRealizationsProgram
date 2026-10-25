import polyak.ModeLocking.Regular.Uniqueness
import polyak.ModeLocking.Regular.Threshold

/-! Exact periods are characterized by the entire fixed support, without
restricting the candidate periodic measure to finitely many atoms in advance. -/
noncomputable section
namespace polyak.ModeLocking.RegularData
open General Levels MeasureTheory
open scoped BigOperators
variable {q : Tuning} {s : ℝ} {L : ℕ} (D : RegularData q s L)

theorem measure_carried_iff (A : Set Frequency) : (∀ᵐ ω ∂D.measure, ω ∈ A) ↔
    ∀ i, D.atoms i ∈ A := by
  classical
  unfold measure atomicMeasure
  rw [ae_finsetSum_measure_iff]
  constructor
  · intro h i
    have hi := h i (Finset.mem_univ i)
    have hp : (D.primal i : ENNReal) ≠ 0 := by exact_mod_cast (D.primal_pos i).ne'
    rw [Measure.ae_ennreal_smul_measure_iff hp, ae_dirac_eq] at hi
    exact hi
  · intro h i _
    exact Measure.ae_smul_measure (by rw [ae_dirac_eq]; exact h i) _

theorem periodic_iff_support (k : ℕ) : PeriodicFP (Geometry.shiftedCurve q s) k ↔
    ∀ i, D.atoms i ∈ periodicGrid k := by
  constructor
  · rintro ⟨w, hw, hcar⟩
    obtain ⟨c, a, hc, he, _⟩ := D.extremal_classification
      (fun n hn => D.lags_nonzero n hn) hw
    rw [he] at hcar
    have hsmul : ∀ᵐ ω ∂((c : ENNReal) • D.measure), ω ∈ periodicGrid k :=
      ae_mono (Measure.le_add_right (le_refl ((c : ENNReal) • D.measure))) hcar
    have hcn : (c : ENNReal) ≠ 0 := by exact_mod_cast hc.ne'
    rw [Measure.ae_ennreal_smul_measure_iff hcn] at hsmul
    exact (D.measure_carried_iff _).mp hsmul
  · intro h
    exact ⟨D.measure, D.primal_feasible, (D.measure_carried_iff _).mpr h⟩

end polyak.ModeLocking.RegularData
