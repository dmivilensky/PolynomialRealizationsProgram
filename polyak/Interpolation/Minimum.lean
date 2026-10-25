import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Tactic

/-!
Article: Appendix A, existence of the minimizer in the conjugate construction.
Use: a direct Hilbert-space argument for strongly convex closed epigraphs,
without a finite-dimensionality or weak-sequential-compactness assumption.
Proof: a minimizing sequence is Cauchy by the quantitative midpoint gap.
Source: the standard direct proof for strongly convex functions on a Hilbert space.
-/

noncomputable section

open Filter Set
open scoped Topology

namespace polyak.Interpolation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Article: Appendix A, minimizing a proper strongly convex epigraph.
Use: handles unbounded data through an epigraph rather than a real-valued supremum.
Proof: choose heights tending to their infimum; the midpoint gap forces the points
in a minimizing sequence to be Cauchy, and closedness supplies its limit. -/
theorem exists_min_height {S : Set (E × ℝ)} (hne : S.Nonempty) (hclosed : IsClosed S)
    (hbdd : BddBelow (Prod.snd '' S)) {c : ℝ} (hc : 0 < c)
    (hmid : ∀ p ∈ S, ∀ q ∈ S,
      (((1 / 2 : ℝ) • (p.1 + q.1)), (p.2 + q.2) / 2 - c * ‖p.1 - q.1‖ ^ 2) ∈ S) :
    ∃ p ∈ S, ∀ q ∈ S, p.2 ≤ q.2 := by
  let m := sInf (Prod.snd '' S)
  obtain ⟨u, _, hut, hu⟩ := exists_seq_tendsto_sInf (hne.image Prod.snd) hbdd
  choose p hp hpu using hu
  have hm : ∀ q ∈ S, m ≤ q.2 := fun q hq => csInf_le hbdd ⟨q, hq, rfl⟩
  have huc : CauchySeq (fun n => (p n).1) := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    have hpos : 0 < c * ε ^ 2 := by positivity
    have he : m < m + c * ε ^ 2 := by linarith
    obtain ⟨N, hN⟩ := eventually_atTop.mp ((tendsto_order.mp hut).2 _ he)
    refine ⟨N, fun n hn k hk => ?_⟩
    have hmn := hm _ (hmid (p n) (hp n) (p k) (hp k))
    rw [hpu n, hpu k] at hmn
    have hn' := hN n hn
    have hk' := hN k hk
    rw [dist_eq_norm]
    by_contra h
    have hsq : ε ^ 2 ≤ ‖(p n).1 - (p k).1‖ ^ 2 :=
      pow_le_pow_left₀ (le_of_lt hε) (le_of_not_gt h) 2
    have hmul := mul_le_mul_of_nonneg_left hsq (le_of_lt hc)
    linarith
  obtain ⟨y, hy⟩ := cauchySeq_tendsto_of_complete huc
  have hpt : Tendsto p atTop (𝓝 (y, m)) := by
    apply Tendsto.prodMk_nhds hy
    simpa only [hpu] using hut
  have hmem : (y, m) ∈ S := hclosed.mem_of_tendsto hpt (Eventually.of_forall hp)
  exact ⟨(y, m), hmem, hm⟩

end polyak.Interpolation
