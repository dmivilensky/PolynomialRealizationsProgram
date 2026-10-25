import polyak.ModeLocking.Boundary.Frontier
import polyak.Levels.Chart.GapOpen
import polyak.Levels.Chart.GapConnected
import Mathlib.Topology.Order.IntermediateValue

/-! The zero set in each actual gap separates the two strict threshold
regions.  The path statement has no regularity or uniqueness hypothesis. -/
noncomputable section
namespace polyak.GapEdges
open General Levels Set

def positiveGap (K : ℕ) : Set Tuning :=
  {q | Geometry.Gap K q ∧ 0 < Threshold.sigma q}

def negativeGap (K : ℕ) : Set Tuning :=
  {q | Geometry.Gap K q ∧ Threshold.sigma q < 0}

theorem positiveGap_isOpen (K : ℕ) : IsOpen (positiveGap K) :=
  (Chart.isOpen_gap K).inter
    (isOpen_lt continuous_const Global.Threshold.continuous_sigma)

theorem negativeGap_isOpen (K : ℕ) : IsOpen (negativeGap K) :=
  (Chart.isOpen_gap K).inter
    (isOpen_lt Global.Threshold.continuous_sigma continuous_const)

theorem boundaryInGap_eq_zero (K : ℕ) :
    ModeLocking.BoundaryInGap K = {q | Geometry.Gap K q ∧ Threshold.sigma q = 0} := by
  ext q
  simp only [ModeLocking.BoundaryInGap, mem_inter_iff, mem_ofPred_eq,
    ModeLocking.mem_frontier_iff_sigma_zero, and_comm]

theorem path_meets_boundary {K : ℕ} {qp qm : Tuning}
    (hp : qp ∈ positiveGap K) (hm : qm ∈ negativeGap K)
    (p : Path qp qm) (hpath : ∀ t, Geometry.Gap K (p t)) :
    ∃ t, p t ∈ ModeLocking.BoundaryInGap K := by
  have hc : Continuous (fun t => Threshold.sigma (p t)) :=
    Global.Threshold.continuous_sigma.comp p.continuous
  obtain ⟨t, ht⟩ := intermediate_value_univ (1 : unitInterval) 0 hc
    (show (0 : ℝ) ∈ Icc (Threshold.sigma (p 1)) (Threshold.sigma (p 0)) by
      simpa only [Path.target, Path.source, mem_Icc] using And.intro hm.2.le hp.2.le)
  refine ⟨t, ?_⟩
  rw [boundaryInGap_eq_zero]
  exact ⟨hpath t, ht⟩

theorem boundaryInGap_nonempty_of_signs {K : ℕ} (hK : 2 ≤ K)
    (hp : (positiveGap K).Nonempty) (hm : (negativeGap K).Nonempty) :
    (ModeLocking.BoundaryInGap K).Nonempty := by
  obtain ⟨qp, hqp⟩ := hp
  obtain ⟨qm, hqm⟩ := hm
  obtain ⟨q, hq, hz⟩ := (Chart.isConnected_gap hK).isPreconnected.intermediate_value
    hqm.1 hqp.1 Global.Threshold.continuous_sigma.continuousOn
    (show (0 : ℝ) ∈ Icc (Threshold.sigma qm) (Threshold.sigma qp) from
      ⟨hqm.2.le, hqp.2.le⟩)
  refine ⟨q, ?_⟩
  rw [boundaryInGap_eq_zero]
  exact ⟨hq, hz⟩

end polyak.GapEdges
