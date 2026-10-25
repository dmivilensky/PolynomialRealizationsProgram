import polyak.CertifiedExamples.Exact313.Results
import polyak.ModeLocking.Regular.Uniqueness
import polyak.GapEdges.Boundary.OmegaOne

/-!
# Direct article statements for the final appendices

These consequences retain the hypotheses and all finite Borel measures of the
article. In particular, the concrete example has no assumed regularity data,
and the neighborhood alternatives keep their phase-locking hypotheses.
-/

noncomputable section
namespace polyak.ArticleResults
open General Levels ModeLocking Set Filter MeasureTheory
open scoped Topology

/-- Theorem G.15 (TeX `thm:exact313`): every threshold spectrum of the
concrete tuning is the same two-frequency measure up to positive scaling
and the admissible atom at zero. The regular witness is constructed. -/
theorem exact313_extremals :
    ∃ R : RegularData CertifiedExamples.Exact313.qStar 0 13,
      Set.range R.atoms = Set.range CertifiedExamples.Exact313.atoms ∧
      ∀ w : Measure Frequency,
        ProgramSolution (tuningCurve CertifiedExamples.Exact313.qStar) nonzeroLags w ↔
          ∃ c a : NNReal, 0 < c ∧
            w = (c : ENNReal) • R.measure +
              (a : ENNReal) • Measure.dirac frequencyZero ∧
            (a : ℝ) ≤ (c : ℝ) *
              ∫ ω, (tuningCurve CertifiedExamples.Exact313.qStar).minimizer ω ∂R.measure := by
  obtain ⟨R, hS, _⟩ := CertifiedExamples.Exact313.exactData.exists_regularData
  refine ⟨R, hS, ?_⟩
  intro w
  simpa only [Geometry.shiftedCurve_zero] using
    R.extremal_iff (N' := nonzeroLags) (fun n hn => R.lags_nonzero n hn) (fun _ h => h) w

/-- Corollary I.1 (TeX `cor:omega1`), first case: a nonlocked point of
`∂Ω₁` has a whole open neighborhood disjoint from the divergence set. -/
theorem omega_one_nonlocked (q : Tuning)
    (hq : q ∈ frontier {p : Tuning | Regions.OmegaOne p})
    (hn : ¬Geometry.PhaseLockedContact q) :
    ∃ V : Set Tuning, IsOpen V ∧ q ∈ V ∧ V ∩ Regions.divergenceSet = ∅ :=
  GapEdges.nonlocked_frontier_neighborhood q hq hn

/-- Corollary I.1 (TeX `cor:omega1`), second case: near a `k`-tongue tip,
the full divergence set is exactly the closed single-frequency tongue. -/
theorem omega_one_tip {q : Tuning} {k : ℕ} (T : GapEdges.Tip q k) :
    ∃ V : Set Tuning, IsOpen V ∧ q ∈ V ∧
      ∀ p ∈ V, p ∈ Regions.divergenceSet ↔
        p.angle (2 * Real.pi / k) ≤ Real.pi / k := by
  obtain ⟨V, hVsub, hV, hqV⟩ := mem_nhds_iff.mp T.closed_tongue_near
  exact ⟨V, hV, hqV, fun p hp => (hVsub hp).1⟩

end polyak.ArticleResults
