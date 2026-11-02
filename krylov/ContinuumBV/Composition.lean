import Mathlib.Analysis.BoundedVariation
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.MeasureTheory.VectorMeasure.IntegrationByParts

/-!
Article: main_krylov, apC:lem:fund, nonlinear potential along BV state paths.
Use: establish actual bounded variation of a C¹ state potential and control
all of its jumps, including an arbitrary countable collection of atoms.
Source: mathlib's local C¹-to-Lipschitz theorem and compactness and the
Stieltjes vector measure associated to bounded variation functions.

This module proves composition regularity and the complete countable jump
sum. It does not assert the continuous nonlinear BV chain rule.
-/

namespace krylov.ContinuumBV
noncomputable section
open Set Filter MeasureTheory
open scoped Topology Function

variable {E : Type*} [NormedAddCommGroup E]

/-- Product paths have no more variation than the sum of their coordinate
variations. This supplies BV of the actual three physical coordinates. -/
theorem eVariationOn_prod_mk_le {α A B : Type*} [LinearOrder α]
    [PseudoEMetricSpace A] [PseudoEMetricSpace B] (f : α → A) (g : α → B) (s : Set α) :
    eVariationOn (fun x => (f x, g x)) s ≤ eVariationOn f s + eVariationOn g s := by
  apply iSup_le
  rintro ⟨n, ⟨u, hu, hmem⟩⟩
  calc
    (∑ i ∈ Finset.range n, edist (f (u (i + 1)), g (u (i + 1))) (f (u i), g (u i))) ≤
        ∑ i ∈ Finset.range n,
          (edist (f (u (i + 1))) (f (u i)) + edist (g (u (i + 1))) (g (u i))) := by
      apply Finset.sum_le_sum
      intro i _hi
      rw [Prod.edist_eq]
      exact max_le_add_of_nonneg zero_le zero_le
    _ = (∑ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i))) +
        ∑ i ∈ Finset.range n, edist (g (u (i + 1))) (g (u i)) := Finset.sum_add_distrib
    _ ≤ _ := add_le_add (eVariationOn.sum_le hu hmem) (eVariationOn.sum_le hu hmem)

/-- BV of both coordinates proves BV of their genuine product path. -/
theorem boundedVariation_prod_mk {α A B : Type*} [LinearOrder α]
    [PseudoEMetricSpace A] [PseudoEMetricSpace B] {f : α → A} {g : α → B} {s : Set α}
    (hf : BoundedVariationOn f s) (hg : BoundedVariationOn g s) :
    BoundedVariationOn (fun x => (f x, g x)) s :=
  ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hf, hg⟩) (eVariationOn_prod_mk_le f g s)

/-- A genuine C¹ function of a BV state has bounded variation when its state
range is contained in a compact set. -/
theorem boundedVariation_comp_contDiff [NormedSpace ℝ E] {z : ℝ → E} {F : E → ℝ} {s : Set E}
    (hz : BoundedVariationOn z univ) (hc : IsCompact s)
    (hmap : MapsTo z univ s) (hF : ∀ w ∈ s, ContDiffAt ℝ 1 F w) :
    BoundedVariationOn (F ∘ z) univ := by
  have hlocal : LocallyLipschitzOn s F := by
    intro w hw
    obtain ⟨C, t, ht, hC⟩ := (hF w hw).exists_lipschitzOnWith
    exact ⟨C, t, mem_nhdsWithin_of_mem_nhds ht, hC⟩
  obtain ⟨C, hC⟩ := hlocal.exists_lipschitzOnWith_of_compact hc
  exact hC.comp_boundedVariationOn hmap hz

/-- The one-sided limit of a BV state remains in its closed state domain. -/
theorem leftLim_mem_of_closed [CompleteSpace E] {z : ℝ → E} {s : Set E}
    (hz : BoundedVariationOn z univ) (hs : IsClosed s) (hmap : MapsTo z univ s) (x : ℝ) :
    Function.leftLim z x ∈ s := by
  apply hs.mem_of_tendsto (hz.tendsto_leftLim x)
  exact Eventually.of_forall (fun t => hmap (mem_univ t))

/-- Right limits satisfy the same closed-domain condition. -/
theorem rightLim_mem_of_closed [CompleteSpace E] {z : ℝ → E} {s : Set E}
    (hz : BoundedVariationOn z univ) (hs : IsClosed s) (hmap : MapsTo z univ s) (x : ℝ) :
    Function.rightLim z x ∈ s := by
  apply hs.mem_of_tendsto (hz.tendsto_rightLim x)
  exact Eventually.of_forall (fun t => hmap (mem_univ t))

/-- A continuous nonlinear potential respects the left state limit. -/
theorem leftLim_comp [CompleteSpace E] {z : ℝ → E} {F : E → ℝ} (hz : BoundedVariationOn z univ)
    {x : ℝ} (hF : ContinuousAt F (Function.leftLim z x)) :
    Function.leftLim (F ∘ z) x = F (Function.leftLim z x) :=
  leftLim_eq_of_tendsto (hF.tendsto.comp (hz.tendsto_leftLim x))

/-- A continuous nonlinear potential respects the right state limit. -/
theorem rightLim_comp [CompleteSpace E] {z : ℝ → E} {F : E → ℝ} (hz : BoundedVariationOn z univ)
    {x : ℝ} (hF : ContinuousAt F (Function.rightLim z x)) :
    Function.rightLim (F ∘ z) x = F (Function.rightLim z x) :=
  rightLim_eq_of_tendsto (hF.tendsto.comp (hz.tendsto_rightLim x))

/-- All jumps of a scalar BV potential form an unconditionally convergent
series over any countable distinct family of locations. The sum is the actual
Stieltjes vector measure of those atoms, not an assumed jump decomposition. -/
theorem hasSum_potential_jumps {ι : Type*} [Countable ι]
    {q : ℝ → ℝ} (hq : BoundedVariationOn q univ)
    (e : ι → ℝ) (he : Function.Injective e) :
    HasSum (fun i => Function.rightLim q (e i) - Function.leftLim q (e i))
      (hq.vectorMeasure (range e)) := by
  have hdisj : Pairwise (Disjoint on fun i => ({e i} : Set ℝ)) := by
    intro i j hij
    exact disjoint_singleton.2 (he.ne hij)
  have hsum := hq.vectorMeasure.hasSum_of_disjoint_iUnion
    (fun i => measurableSet_singleton (e i)) hdisj
  simpa only [hq.vectorMeasure_singleton, iUnion_singleton_eq_range] using hsum

/-- Countably many scalar potential jumps are absolutely summable.
This supplies the summability step needed before inserting all atom losses. -/
theorem summable_abs_potential_jumps {ι : Type*} [Countable ι]
    {q : ℝ → ℝ} (hq : BoundedVariationOn q univ)
    (e : ι → ℝ) (he : Function.Injective e) :
    Summable (fun i => |Function.rightLim q (e i) - Function.leftLim q (e i)|) := by
  simpa only [Real.norm_eq_abs] using
    summable_norm_iff.2 (hasSum_potential_jumps hq e he).summable

end
end krylov.ContinuumBV
