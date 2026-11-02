import krylov.LotkaVolterra.OrbitEstimates
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.Monotone
import Mathlib.Topology.Order.Lattice

/-!
Article: `main_krylov`, `apC:prop:g1`, forward invariance of the escape wedge.

A compact first-exit argument for two scalar strict barriers. The conclusion
concerns actual differentiable curves, not just the signs of a vector field.
Source: the standard first-contact proof of strict forward invariance.
-/
namespace krylov.LotkaVolterra
noncomputable section
open Set Filter
open scoped Topology

/-- At a first zero approached through positive values from the left, a
strictly positive derivative is impossible. -/
theorem not_pos_derivative_at_first_zero {f : ℝ → ℝ} {a c v : ℝ}
    (hac : a < c) (hf : HasDerivAt f v c) (hfc : f c = 0)
    (hbefore : ∀ t ∈ Ioo a c, 0 < f t) : ¬ 0 < v := by
  intro hv
  have hslope : ∀ᶠ t in 𝓝[<] c, 0 < slope f c t :=
    ((hasDerivAt_iff_tendsto_slope_left_right.mp hf).1).eventually
      (Ioi_mem_nhds hv)
  have hright : ∀ᶠ t in 𝓝[<] c, a < t :=
    nhdsWithin_le_nhds (Ioi_mem_nhds hac)
  have hleft : ∀ᶠ t in 𝓝[<] c, t < c := self_mem_nhdsWithin
  obtain ⟨t, ht, hat, hsl⟩ :=
    (hleft.and (hright.and hslope)).exists
  have hpos := hbefore t ⟨hat, ht⟩
  rw [slope_def_field, hfc, sub_zero] at hsl
  have hn : f t / (t - c) < 0 := div_neg_of_pos_of_neg hpos (by linarith)
  linarith

/-- Two strict barriers remain positive. The second boundary only needs an
inward derivative when the first barrier is strictly positive: simultaneous
contact is already excluded by the first boundary condition. -/
theorem pair_positive_invariant {f g f' g' : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b)
    (hf : ∀ t ∈ Icc a b, HasDerivAt f (f' t) t)
    (hg : ∀ t ∈ Icc a b, HasDerivAt g (g' t) t)
    (hfa : 0 < f a) (hga : 0 < g a)
    (hfin : ∀ t ∈ Icc a b, f t = 0 → 0 ≤ g t → 0 < f' t)
    (hgin : ∀ t ∈ Icc a b, g t = 0 → 0 < f t → 0 < g' t) :
    0 < f b ∧ 0 < g b := by
  by_contra hbad
  let m : ℝ → ℝ := fun t ↦ min (f t) (g t)
  let C : Set ℝ := Icc a b ∩ m ⁻¹' Iic 0
  have hc : ContinuousOn m (Icc a b) :=
    (HasDerivAt.continuousOn hf).inf (HasDerivAt.continuousOn hg)
  have hC : IsClosed C := hc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have hbC : b ∈ C := by
    refine ⟨⟨hab, le_rfl⟩, ?_⟩
    change min (f b) (g b) ≤ 0
    by_contra! hm
    exact hbad (lt_min_iff.mp hm)
  have hbdd : BddBelow C := ⟨a, fun _ ht ↦ ht.1.1⟩
  have hleast := hC.isLeast_csInf ⟨b, hbC⟩ hbdd
  let c := sInf C
  have hcC : c ∈ C := hleast.1
  have hac : a < c := by
    have haC : a ∉ C := by
      intro haC
      have hm : 0 < min (f a) (g a) := lt_min hfa hga
      exact (not_le_of_gt hm) haC.2
    exact lt_of_le_of_ne hcC.1.1 (by intro he; exact haC (he ▸ hcC))
  have hbefore : ∀ t ∈ Ioo a c, 0 < f t ∧ 0 < g t := by
    intro t ht
    have htnot : t ∉ C := by
      intro htC
      exact (not_le_of_gt ht.2) (hleast.2 htC)
    have hm : 0 < min (f t) (g t) := by
      by_contra! hm
      exact htnot ⟨⟨ht.1.le, ht.2.le.trans hcC.1.2⟩, hm⟩
    exact lt_min_iff.mp hm
  have hleft : ∀ᶠ t in 𝓝[<] c, t ∈ Ioo a c := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Ioi_mem_nhds hac)] with t ht hat
    exact ⟨hat, ht⟩
  have hfc : 0 ≤ f c := ge_of_tendsto
    ((hf c hcC.1).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    (hleft.mono fun _ ht ↦ (hbefore _ ht).1.le)
  have hgc : 0 ≤ g c := ge_of_tendsto
    ((hg c hcC.1).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    (hleft.mono fun _ ht ↦ (hbefore _ ht).2.le)
  rcases eq_or_lt_of_le hfc with hfc | hfc
  · exact not_pos_derivative_at_first_zero hac (hf c hcC.1) hfc.symm
      (fun t ht ↦ (hbefore t ht).1) (hfin c hcC.1 hfc.symm hgc)
  · have hgzero : g c = 0 := by
      have hm : min (f c) (g c) ≤ 0 := hcC.2
      rcases le_total (f c) (g c) with hfg | hgf
      · rw [min_eq_left hfg] at hm
        linarith
      · rw [min_eq_right hgf] at hm
        exact le_antisymm hm hgc
    exact not_pos_derivative_at_first_zero hac (hg c hcC.1) hgzero
      (fun t ht ↦ (hbefore t ht).2) (hgin c hcC.1 hgzero hfc)

end
end krylov.LotkaVolterra
