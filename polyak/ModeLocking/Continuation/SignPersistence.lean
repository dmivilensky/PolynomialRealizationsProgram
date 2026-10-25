import polyak.ModeLocking.Continuation.ActualSlacks
import polyak.ModeLocking.Analysis.AnalyticPersistence

/-! Primary regularity gives a quantitative global negative jet cover, and
the exact continued value/slope equations preserve that cover. -/
noncomputable section
namespace polyak.ModeLocking.RegularData
open General Levels Filter Set
open scoped BigOperators Topology
variable {q : Tuning} {s : ℝ} {L : ℕ} (D : RegularData q s L)

def zeroCenters : Finset ℝ := by
  classical
  exact insert 0 (Finset.univ.image (fun i => (D.atoms i : ℝ)))

theorem mem_zeroCenters (x : ℝ) : x ∈ D.zeroCenters ↔ x = 0 ∨ ∃ i, x = (D.atoms i : ℝ) := by
  classical
  simp only [zeroCenters, Finset.mem_insert, Finset.mem_image, Finset.mem_univ, true_and]
  exact or_congr_right (by constructor <;> rintro ⟨i, hi⟩ <;> exact ⟨i, hi.symm⟩)

theorem negativeJetCover : Nonempty (Analysis.NegativeJetCover 0 Real.pi D.zeroCenters
    (finiteSymbol q s D.lags D.dual)) := by
  classical
  apply Analysis.exists_negativeJetCover
  · exact ⟨0, (D.mem_zeroCenters 0).mpr (Or.inl rfl)⟩
  · intro z hz
    rcases (D.mem_zeroCenters z).mp hz with rfl | ⟨i, rfl⟩
    · exact ⟨le_rfl, Real.pi_pos.le⟩
    · exact (D.atoms i).property
  · intro x hx
    exact (analyticAt_finiteSymbol q s D.lags D.dual hx).contDiffAt
  · intro x hx
    rw [iteratedDeriv_eq_iterate]
    exact (analyticAt_finiteSymbol q s D.lags D.dual hx).deriv.deriv.continuousAt.continuousWithinAt
  · intro z hz
    rcases (D.mem_zeroCenters z).mp hz with rfl | ⟨i, rfl⟩
    · exact D.symbol_zero_endpoint
    · exact D.symbol_zero_support i
  · intro z hz
    rcases (D.mem_zeroCenters z).mp hz with rfl | ⟨i, rfl⟩
    · exact D.symbol_slope_zero
    · exact D.symbol_slope_support i
  · intro z hz
    rw [iteratedDeriv_eq_iterate]
    rcases (D.mem_zeroCenters z).mp hz with rfl | ⟨i, rfl⟩
    · exact D.symbol_curvature_zero
    · exact D.support_curvature i
  · intro x hx hn
    have hzero : x ≠ 0 := fun he => hn ((D.mem_zeroCenters x).mpr (Or.inl he))
    have hpos : 0 < x := lt_of_le_of_ne hx.1 hzero.symm
    exact D.dual_strict x hpos hx.2 (fun i hi => hn ((D.mem_zeroCenters x).mpr (Or.inr ⟨i, hi⟩)))

namespace ContinuationData
variable {D} (C : D.ContinuationData)

theorem negative_cover_near : ∀ᶠ q' in 𝓝 q,
    Nonempty (Analysis.NegativeJetCover 0 Real.pi D.zeroCenters
      (finiteSymbol q' (C.shift (Continuation.parameters q')) D.lags (C.weight (Continuation.parameters q')))) := by
  classical
  obtain ⟨B⟩ := D.negativeJetCover
  have hbase : Analysis.NegativeJetCover 0 Real.pi D.zeroCenters
      (fun x => C.jointSymbol (Continuation.parameters q, x)) := by
    have he : (fun x => C.jointSymbol (Continuation.parameters q, x)) = finiteSymbol q s D.lags D.dual :=
      funext C.jointSymbol_base
    rw [he]
    exact B
  have hqeq := Continuation.continuous_parameters.continuousAt.eventually C.equations
  have hjets : ∀ᶠ q' in 𝓝 q, ∀ z ∈ D.zeroCenters,
      C.jointSymbol (Continuation.parameters q', z) = 0 ∧
        deriv (fun x => C.jointSymbol (Continuation.parameters q', x)) z = 0 := by
    filter_upwards [hqeq] with q' hq' z hz
    rcases (D.mem_zeroCenters z).mp hz with rfl | ⟨i, rfl⟩
    · exact ⟨C.jointSymbol_zero q', C.jointSymbol_slope_zero q'⟩
    · exact ⟨C.symbol_support_zero hq'.2.1 i,
        C.symbol_support_slope_zero hq'.2.2.2.2.1 i⟩
  have hh := hbase.eventually_persist_of_analytic_pullback Continuation.continuous_parameters
    (fun x hx => C.analyticAt_jointSymbol hx) hjets
  exact hh

end ContinuationData
end polyak.ModeLocking.RegularData
