import krylov.ContinuumBV.CadlagPartitions
import krylov.ContinuumBV.DensityPartitions

/-!
Article: main_krylov, apC:lem:fund, general physical state measures.
Use: identify the nonlinear graph-completed chain with the two genuine
physical density integrals. The state and coefficients may jump at countably
many atoms; all integrals are identified by exact common partition sums.
Source: interval state equations, chord FTC and dominated convergence.
-/

namespace krylov.ContinuumBV
noncomputable section
open Set Filter MeasureTheory
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Graph-completed coefficients act integrably on every actual integrable
state density supported in the physical window, including atomic densities. -/
theorem C1ChordPartitions.action_integrable {z : ℝ → E} {F : E → ℝ} {a b : ℝ}
    (p : C1ChordPartitions z F a b) (hz : BoundedVariationOn z univ)
    (hright : ∀ x ∈ Icc a b, ContinuousWithinAt z (Ici x) x)
    (hFjump : ∀ x ∈ Ioc a b, ∀ w ∈ segment ℝ (Function.leftLim z x) (z x),
      ContDiffAt ℝ 1 F w)
    {μ : Measure ℝ} {h : ℝ → E} (hs : ∀ᵐ x ∂μ, x ∈ Ioc a b) (hi : Integrable h μ) :
    Integrable (fun x => chordCoefficient F (Function.leftLim z x) (z x) (h x)) μ := by
  let A : ℕ → ℕ → Set ℝ := fun k i => Ioc (p.time k i) (p.time k (i + 1))
  let c : ℕ → ℕ → E →L[ℝ] ℝ := fun k i =>
    chordCoefficient F (z (p.time k i)) (z (p.time k (i + 1)))
  have hdisj : ∀ k, (Finset.range (p.size k) : Set ℕ).PairwiseDisjoint (A k) := by
    intro k i _ j _ hij
    rcases lt_or_gt_of_ne hij with hij | hji
    · exact Ioc_disjoint_Ioc_of_le (p.monotone k (Nat.succ_le_of_lt hij))
    · exact (Ioc_disjoint_Ioc_of_le (p.monotone k (Nat.succ_le_of_lt hji))).symm
  have hcover : ∀ k, ∀ᵐ x ∂μ, ∃ i ∈ Finset.range (p.size k), x ∈ A k i := by
    intro k
    filter_upwards [hs] with x hx
    have hx' : x ∈ Ioc (p.time k 0) (p.time k (p.size k)) := by
      simpa only [p.initial k, p.terminal k] using hx
    obtain ⟨i, hi, hxi⟩ := (show ∃ i, ∃ hi : i ∈ Finset.range (p.size k),
        x ∈ Ioc (p.time k i) (p.time k (i + 1)) from by
      simpa only [mem_iUnion] using Ioc_subset_biUnion_Ioc (p.size k) (p.time k) hx')
    exact ⟨i, hi, hxi⟩
  obtain ⟨C, hC⟩ := p.bounded
  apply density_partition_limit_integrable hi (fun k => Finset.range (p.size k)) A c
    (fun _ _ _ => measurableSet_Ioc) hdisj hcover
    ⟨C, fun k i hi => norm_chordCoefficient_le (hC k i (Finset.mem_range.1 hi))⟩
  filter_upwards [hs] with x hx
  exact chord_partitionCoefficient_tendsto hz p.time p.size p.tolerance p.monotone p.initial p.terminal
    p.mesh p.tendsto_tolerance hright p.regular hFjump p.bounded hx

/-- Physical nonlinear BV identity, with arbitrary jumps and singular mass.
The interval increment equation is a genuine linear state equation, while
the nonlinear identity itself is derived from exact chord partition sums. -/
theorem cadlag_physical_chain_of_partitions {z : ℝ → E} (hz : BoundedVariationOn z univ)
    {F : E → ℝ} {a b : ℝ} (t : ℕ → ℕ → ℝ) (n : ℕ → ℕ) (δ : ℕ → ℝ)
    (ht : ∀ k, Monotone (t k)) (ha : ∀ k, t k 0 = a) (hb : ∀ k, t k (n k) = b)
    (hmesh : ∀ k i, i < n k → t k (i + 1) - t k i ≤ δ k)
    (hδ : Tendsto δ atTop (𝓝 0))
    (hright : ∀ x ∈ Icc a b, ContinuousWithinAt z (Ici x) x)
    (hF : ∀ k i, i < n k → ∀ w ∈ segment ℝ (z (t k i)) (z (t k (i + 1))),
      ContDiffAt ℝ 1 F w)
    (hFjump : ∀ x ∈ Ioc a b, ∀ w ∈ segment ℝ (Function.leftLim z x) (z x),
      ContDiffAt ℝ 1 F w)
    (hbound : ∃ C, ∀ k i, i < n k → ∀ w ∈ segment ℝ (z (t k i)) (z (t k (i + 1))),
      ‖fderiv ℝ F w‖ ≤ C)
    (μ₁ μ₂ : Measure ℝ) (h₁ h₂ : ℝ → E)
    (hs₁ : ∀ᵐ x ∂μ₁, x ∈ Ioc a b) (hs₂ : ∀ᵐ x ∂μ₂, x ∈ Ioc a b)
    (hi₁ : Integrable h₁ μ₁) (hi₂ : Integrable h₂ μ₂)
    (hinc : ∀ u v, u ∈ Icc a b → v ∈ Icc a b → u ≤ v →
      z v - z u = (∫ x in Ioc u v, h₁ x ∂μ₁) + (∫ x in Ioc u v, h₂ x ∂μ₂)) :
    (∫ x, chordCoefficient F (Function.leftLim z x) (z x) (h₁ x) ∂μ₁) +
      (∫ x, chordCoefficient F (Function.leftLim z x) (z x) (h₂ x) ∂μ₂) = F (z b) - F (z a) := by
  let A : ℕ → ℕ → Set ℝ := fun k i => Ioc (t k i) (t k (i + 1))
  let c : ℕ → ℕ → E →L[ℝ] ℝ := fun k i => chordCoefficient F (z (t k i)) (z (t k (i + 1)))
  have hdisj : ∀ k, (Finset.range (n k) : Set ℕ).PairwiseDisjoint (A k) := by
    intro k i _ j _ hij
    rcases lt_or_gt_of_ne hij with hij | hji
    · exact Ioc_disjoint_Ioc_of_le (ht k (Nat.succ_le_of_lt hij))
    · exact (Ioc_disjoint_Ioc_of_le (ht k (Nat.succ_le_of_lt hji))).symm
  have hcover : ∀ k x, x ∈ Ioc a b → ∃ i ∈ Finset.range (n k), x ∈ A k i := by
    intro k x hx
    have hx' : x ∈ Ioc (t k 0) (t k (n k)) := by simpa only [ha k, hb k] using hx
    obtain ⟨i, hi, hxi⟩ := (show ∃ i, ∃ hi : i ∈ Finset.range (n k),
        x ∈ Ioc (t k i) (t k (i + 1)) from by
      simpa only [mem_iUnion] using Ioc_subset_biUnion_Ioc (n k) (t k) hx')
    exact ⟨i, hi, hxi⟩
  obtain ⟨C, hC⟩ := hbound
  have hc : ∃ C, ∀ k i, i ∈ Finset.range (n k) → ‖c k i‖ ≤ C :=
    ⟨C, fun k i hi => norm_chordCoefficient_le (hC k i (Finset.mem_range.1 hi))⟩
  have hlim : ∀ x ∈ Ioc a b, Tendsto
      (fun k => partitionCoefficient (Finset.range (n k)) (A k) (c k) x) atTop
      (𝓝 (chordCoefficient F (Function.leftLim z x) (z x))) := by
    intro x hx
    exact chord_partitionCoefficient_tendsto hz t n δ ht ha hb hmesh hδ hright hF hFjump ⟨C, hC⟩ hx
  have hlim₁ := density_partition_sums_tendsto hi₁ (fun k => Finset.range (n k)) A c
    (fun _ _ _ => measurableSet_Ioc) hdisj
    (fun k => hs₁.mono (hcover k)) hc (hs₁.mono hlim)
  have hlim₂ := density_partition_sums_tendsto hi₂ (fun k => Finset.range (n k)) A c
    (fun _ _ _ => measurableSet_Ioc) hdisj
    (fun k => hs₂.mono (hcover k)) hc (hs₂.mono hlim)
  have hvalue : ∀ k,
      (∑ i ∈ Finset.range (n k), c k i (∫ x in A k i, h₁ x ∂μ₁)) +
        (∑ i ∈ Finset.range (n k), c k i (∫ x in A k i, h₂ x ∂μ₂)) = F (z b) - F (z a) := by
    intro k
    rw [← Finset.sum_add_distrib]
    calc
      _ = ∑ i ∈ Finset.range (n k), (F (z (t k (i + 1))) - F (z (t k i))) := by
        apply Finset.sum_congr rfl
        intro i hi
        have him : i < n k := Finset.mem_range.1 hi
        have hmem : ∀ j, j ≤ n k → t k j ∈ Icc a b := by
          intro j hj
          exact ⟨by rw [← ha k]; exact ht k (Nat.zero_le _), by rw [← hb k]; exact ht k hj⟩
        rw [← map_add, ← hinc _ _ (hmem _ him.le) (hmem _ (Nat.succ_le_of_lt him))
          (ht k (Nat.le_succ i))]
        exact chordCoefficient_apply_sub (hF k i him)
      _ = _ := by simpa only [ha k, hb k] using
        Finset.sum_range_sub (fun j => F (z (t k j))) (n k)
  exact tendsto_nhds_unique (hlim₁.add hlim₂) (by simpa only [hvalue] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => F (z b) - F (z a)) atTop (𝓝 _)))

end
end krylov.ContinuumBV
