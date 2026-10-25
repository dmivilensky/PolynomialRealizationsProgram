import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Instances.Real.Lemmas

/-!
Article: chebyshev2, Theorem E.1.
The compactness argument for strict admissibility in Theorem E.1.
Result: `chebyshev2.DualCertificate.finite_strict_box_stability` supplies the stated article
conclusion.
-/
namespace chebyshev2.DualCertificate
noncomputable section
open Set Filter
open scoped Topology

/--
Establishes the stated eventual or almost-everywhere assertion `∀ᶠ κ in 𝓝 k, 0 < κ ∧ ∀ x, F
(κ,x) < 0`.

Use: `chebyshev2.DualCertificate.finite_strict_box_stability` uses this bound to establish
establishes the stated eventual or almost-everywhere assertion `∀ᶠ κ in 𝓝 k, 0 < κ ∧ ∀ i x, F i
(κ,x) < 0`.

Article: chebyshev2, Theorem E.1.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem strict_box_stability {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {F : ℝ × X → ℝ} {k : ℝ} (hk : 0 < k)
    (hF : ContinuousOn F (Ioi (0:ℝ) ×ˢ univ))
    (hneg : ∀ x, F (k,x) < 0) :
    ∀ᶠ κ in 𝓝 k, 0 < κ ∧ ∀ x, F (κ,x) < 0 := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  have hlocal : ∀ x ∈ (univ : Set X),
      ∀ᶠ z : ℝ × X in 𝓝 (k,x), F z < 0 := by
    intro x _
    -- Establish continuity hc before using the function at limits or in calculus arguments.
    have hc : ContinuousAt F (k,x) := (hF (k,x) ⟨hk,mem_univ _⟩).continuousAt
      ((isOpen_Ioi.prod isOpen_univ).mem_nhds ⟨hk,mem_univ _⟩)
    exact hc.eventually (gt_mem_nhds (hneg x))
  have hall := isCompact_univ.eventually_forall_of_forall_eventually
    (P := fun κ x => F (κ,x)<0) hlocal
  filter_upwards [hall,lt_mem_nhds hk] with κ hκ hkκ
  exact ⟨hkκ,fun x => hκ x (mem_univ _)⟩

/--
Establishes the stated eventual or almost-everywhere assertion `∀ᶠ κ in 𝓝 k, 0 < κ ∧ ∀ i x, F i
(κ,x) < 0`.

Use: a standalone supporting bound for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: chebyshev2, Theorem E.1.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection.
-/
theorem finite_strict_box_stability {ι X : Type*} [Fintype ι]
    [TopologicalSpace X] [CompactSpace X] {F : ι → ℝ × X → ℝ} {k : ℝ}
    (hk : 0 < k) (hF : ∀ i, ContinuousOn (F i) (Ioi (0:ℝ) ×ˢ univ))
    (hneg : ∀ i x, F i (k,x) < 0) :
    ∀ᶠ κ in 𝓝 k, 0 < κ ∧ ∀ i x, F i (κ,x) < 0 := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  have h := Filter.eventually_all.mpr
    (fun i => strict_box_stability hk (hF i) (hneg i))
  filter_upwards [h,lt_mem_nhds hk] with κ hκ hkκ
  exact ⟨hkκ,fun i => (hκ i).2⟩

end
end chebyshev2.DualCertificate
