import polyak.GapEdges.Tips.Persistence

/-! A common open neighborhood for all conclusions of the tips theorem. -/
noncomputable section
namespace polyak.GapEdges.Tip
open General Levels ModeLocking Set Filter MeasureTheory
open scoped Topology
variable {q : Tuning} {k : ℕ} (T : Tip q k)
include T

theorem tips : ∃ V : Set Tuning, IsOpen V ∧ q ∈ V ∧
    ∃ f : Continuation.Parameters → ℝ, ∀ q' ∈ V,
      Threshold.sigma q' = FareyPlateau.Edge.shift q' k (2 * Real.pi / k) ∧
      Threshold.sigmaPeriodic q' k = FareyPlateau.Edge.shift q' k (2 * Real.pi / k) ∧
      AnalyticAt ℝ f (Continuation.parameters q') ∧
      Threshold.sigma q' = f (Continuation.parameters q') ∧
      (q' ∈ Regions.divergenceSet ↔ q'.angle (2 * Real.pi / k) ≤ Real.pi / k) ∧
      (∀ K : ℕ, Geometry.Gap K q' → 0 < Threshold.sigma q') ∧
      (∃ D : RegularData q' (Threshold.sigma q') k,
        Set.range D.atoms = {T.frequency} ∧ D.lags = lags k) ∧
      (∀ w : Measure Frequency,
        ProgramSolution (Geometry.shiftedCurve q' (Threshold.sigma q')) nonzeroLags w ↔
          ∃ c a : NNReal, 0 < c ∧
            w = (c : ENNReal) • Measure.dirac T.frequency +
              (a : ENNReal) • Measure.dirac frequencyZero ∧
            (a : ℝ) ≤ (c : ℝ) * (Geometry.shiftedCurve q' (Threshold.sigma q')).minimizer T.frequency) := by
  obtain ⟨f, hf⟩ := T.analytic_threshold_near
  have hall := T.persistence.and (hf.and (T.closed_tongue_near.and T.extremals_near))
  obtain ⟨V, hsub, hV, hqV⟩ := mem_nhds_iff.mp hall
  refine ⟨V, hV, hqV, f, ?_⟩
  intro q' hq'
  obtain ⟨hD, hA, hC, hE⟩ := hsub hq'
  obtain ⟨D, hS, hN, he, heP⟩ := hD
  exact ⟨he, heP, hA.1, hA.2, hC.1, hC.2, ⟨D, hS, hN⟩, hE⟩

end polyak.GapEdges.Tip
