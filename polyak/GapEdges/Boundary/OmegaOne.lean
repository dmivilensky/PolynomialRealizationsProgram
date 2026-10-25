import polyak.GapEdges.Tips.Persistence
import polyak.GapEdges.Boundary.Diagonal

/-! The complete neighborhood theorem along the lag-one frontier, and
the separation of the closure of every gap boundary from that frontier. -/
noncomputable section
namespace polyak.GapEdges
open General Levels ModeLocking Set Filter
open scoped Topology

theorem omegaOne_frontier_neighborhood (q : Tuning)
    (hq : q ∈ frontier {p : Tuning | Regions.OmegaOne p}) :
    (∃ V : Set Tuning, IsOpen V ∧ q ∈ V ∧ V ∩ Regions.divergenceSet = ∅) ∨
      ∃ k : ℕ, 3 ≤ k ∧ ∃ V : Set Tuning, IsOpen V ∧ q ∈ V ∧
        ∀ p ∈ V, (p ∈ Regions.divergenceSet ↔ p.angle (2 * Real.pi / k) ≤ Real.pi / k) ∧
          (∀ K : ℕ, Geometry.Gap K p → 0 < Threshold.sigma p) := by
  by_cases hl : Geometry.PhaseLockedContact q
  · obtain ⟨k, hk, hphase⟩ := hl
    let T : Tip q k := ⟨hk, hq, hphase⟩
    obtain ⟨V, hsub, hV, hqV⟩ := mem_nhds_iff.mp T.closed_tongue_near
    exact Or.inr ⟨k, hk, V, hV, hqV, fun p hp => hsub hp⟩
  · exact Or.inl (nonlocked_frontier_neighborhood q hq hl)

theorem closure_gap_boundary_disjoint_omegaOne (K : ℕ) :
    closure (BoundaryInGap K) ∩ frontier {p : Tuning | Regions.OmegaOne p} = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro q hq
  rcases omegaOne_frontier_neighborhood q hq.2 with ⟨V, hV, hqV, hdis⟩ |
    ⟨k, _hk, V, hV, hqV, hsub⟩
  · obtain ⟨p, hpV, hpB⟩ := mem_closure_iff.mp hq.1 V hV hqV
    have hpD : p ∈ Regions.divergenceSet := by
      rw [divergenceSet_iff_sigma_nonpos, boundary_sigma_zero hpB]
    have hm : p ∈ V ∩ Regions.divergenceSet := ⟨hpV, hpD⟩
    simp only [hdis, mem_empty_iff_false] at hm
  · obtain ⟨p, hpV, hpB⟩ := mem_closure_iff.mp hq.1 V hV hqV
    have hpos := (hsub p hpV).2 K hpB.2
    rw [boundary_sigma_zero hpB] at hpos
    exact (lt_irrefl 0) hpos

end polyak.GapEdges
