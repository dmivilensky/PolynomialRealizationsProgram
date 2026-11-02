import krylov.ContinuumBV.ChordCoefficient

/-!
Article: main_krylov, apC:lem:fund, countably many nonlinear jumps.
Use: exact chord coefficients on genuine refining physical partitions. Their
pointwise limit uses the true left and right states, including every atom.
Source: the BV one-sided limits, finite partition sums and vector-measure DCT.
-/

namespace krylov.ContinuumBV
noncomputable section
open Set Filter MeasureTheory
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Genuine finite time partitions and C¹ bounds on their state chords.
These data contain no chain rule, nonlinear increment or integral identity. -/
structure C1ChordPartitions (z : ℝ → E) (F : E → ℝ) (a b : ℝ) where
  time : ℕ → ℕ → ℝ
  size : ℕ → ℕ
  tolerance : ℕ → ℝ
  monotone : ∀ k, Monotone (time k)
  initial : ∀ k, time k 0 = a
  terminal : ∀ k, time k (size k) = b
  mesh : ∀ k i, i < size k → time k (i + 1) - time k i ≤ tolerance k
  tendsto_tolerance : Tendsto tolerance atTop (𝓝 0)
  regular : ∀ k i, i < size k → ∀ w ∈ segment ℝ (z (time k i)) (z (time k (i + 1))),
    ContDiffAt ℝ 1 F w
  bounded : ∃ C, ∀ k i, i < size k → ∀ w ∈ segment ℝ (z (time k i)) (z (time k (i + 1))),
    ‖fderiv ℝ F w‖ ≤ C

omit [CompleteSpace E] in
/-- A cell containing x in a vanishing-mesh partition has both endpoints
converging to x. The left endpoint remains strictly below x. -/
theorem partition_endpoints_tendsto {t : ℕ → ℕ → ℝ} {n i : ℕ → ℕ} {δ : ℕ → ℝ} {x : ℝ}
    (hi : ∀ k, i k < n k) (hx : ∀ k, x ∈ Ioc (t k (i k)) (t k (i k + 1)))
    (hmesh : ∀ k j, j < n k → t k (j + 1) - t k j ≤ δ k)
    (hδ : Tendsto δ atTop (𝓝 0)) :
    Tendsto (fun k => t k (i k)) atTop (𝓝 x) ∧
      Tendsto (fun k => t k (i k + 1)) atTop (𝓝 x) := by
  have hleft : Tendsto (fun k => x - t k (i k)) atTop (𝓝 0) := by
    apply squeeze_zero (fun k => (hx k).1.le |> sub_nonneg.2) _ hδ
    intro k
    exact (sub_le_sub_right (hx k).2 _).trans (hmesh k _ (hi k))
  have hright : Tendsto (fun k => t k (i k + 1) - x) atTop (𝓝 0) := by
    apply squeeze_zero (fun k => sub_nonneg.2 (hx k).2) _ hδ
    intro k
    exact (sub_le_sub_left (hx k).1.le _).trans (hmesh k _ (hi k))
  constructor
  · simpa only [sub_sub_cancel, sub_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => x) atTop (𝓝 x)).sub hleft
  · simpa only [sub_add_cancel, zero_add] using hright.add_const x

/-- The actual step averages on vanishing-mesh physical partitions converge
at every point to the average on its true left/post-state chord. -/
theorem chord_partitionCoefficient_tendsto {z : ℝ → E} (hz : BoundedVariationOn z univ)
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
      ‖fderiv ℝ F w‖ ≤ C) {x : ℝ} (hx : x ∈ Ioc a b) :
    Tendsto (fun k => partitionCoefficient (Finset.range (n k))
      (fun i => Ioc (t k i) (t k (i + 1)))
      (fun i => chordCoefficient F (z (t k i)) (z (t k (i + 1)))) x) atTop
      (𝓝 (chordCoefficient F (Function.leftLim z x) (z x))) := by
  have hdisj : ∀ k, (Finset.range (n k) : Set ℕ).PairwiseDisjoint
      (fun i => Ioc (t k i) (t k (i + 1))) := by
    intro k i _ j _ hij
    rcases lt_or_gt_of_ne hij with hij | hji
    · exact Ioc_disjoint_Ioc_of_le (ht k (Nat.succ_le_of_lt hij))
    · exact (Ioc_disjoint_Ioc_of_le (ht k (Nat.succ_le_of_lt hji))).symm
  have hcover : ∀ k, ∃ i ∈ Finset.range (n k), x ∈ Ioc (t k i) (t k (i + 1)) := by
    intro k
    have hx' : x ∈ Ioc (t k 0) (t k (n k)) := by simpa only [ha k, hb k] using hx
    obtain ⟨i, hi, hxi⟩ := (show ∃ i, ∃ hi : i ∈ Finset.range (n k),
        x ∈ Ioc (t k i) (t k (i + 1)) from by
      simpa only [mem_iUnion] using Ioc_subset_biUnion_Ioc (n k) (t k) hx')
    exact ⟨i, hi, hxi⟩
  choose i hi hxi using hcover
  have hi' : ∀ k, i k < n k := fun k => Finset.mem_range.1 (hi k)
  obtain ⟨hl, hr⟩ := partition_endpoints_tendsto hi' hxi hmesh hδ
  have hzl : Tendsto (fun k => z (t k (i k))) atTop (𝓝 (Function.leftLim z x)) :=
    (hz.tendsto_leftLim x).comp (tendsto_nhdsWithin_iff.2
      ⟨hl, Eventually.of_forall (fun k => (hxi k).1)⟩)
  have hzr : Tendsto (fun k => z (t k (i k + 1))) atTop (𝓝 (z x)) :=
    (hright x (Ioc_subset_Icc_self hx)).tendsto.comp (tendsto_nhdsWithin_iff.2
      ⟨hr, Eventually.of_forall (fun k => (hxi k).2)⟩)
  obtain ⟨C, hC⟩ := hbound
  have he := tendsto_chordCoefficient hzl hzr
    (fun k => hF k _ (hi' k)) (hFjump x hx) ⟨C, fun k => hC k _ (hi' k)⟩
  exact he.congr' (Eventually.of_forall (fun k =>
    (partitionCoefficient_eq (hdisj k) (hi k) (hxi k)).symm))

/-- Full nonlinear BV chain identity in graph-completed form. The coefficient
at each jump is the actual average derivative on its true state chord. There
is no atom-size restriction and no assumed integral-limit identity. The C¹
and derivative-bound hypotheses concern only genuine partition and jump chords. -/
theorem cadlag_chain_of_chord_partitions {z : ℝ → E} (hz : BoundedVariationOn z univ)
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
      ‖fderiv ℝ F w‖ ≤ C) :
    (∫ᵛ x in Ioc a b, chordCoefficient F (Function.leftLim z x) (z x)
      ∂[derivativePairing; hz.vectorMeasure]) = F (z b) - F (z a) := by
  let μ := hz.vectorMeasure.restrict (Ioc a b)
  let A : ℕ → ℕ → Set ℝ := fun k i => Ioc (t k i) (t k (i + 1))
  let c : ℕ → ℕ → E →L[ℝ] ℝ := fun k i => chordCoefficient F (z (t k i)) (z (t k (i + 1)))
  let step : ℕ → ℝ → E →L[ℝ] ℝ := fun k => partitionCoefficient (Finset.range (n k)) (A k) (c k)
  have hμvar : μ.variation = hz.vectorMeasure.variation.restrict (Ioc a b) :=
    VectorMeasure.variation_restrict measurableSet_Ioc
  have hsupport : ∀ᵐ x ∂μ.variation, x ∈ Ioc a b := by
    rw [hμvar]
    exact ae_restrict_mem measurableSet_Ioc
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
  have hstepi : ∀ k, μ.Integrable (step k) := by
    intro k
    exact VectorMeasure.Integrable.fun_finsetSum _ (fun i _ =>
      (integrable_const (c k i)).indicator measurableSet_Ioc)
  obtain ⟨C, hC⟩ := hbound
  have hnorm : ∀ k, ∀ᵐ x ∂μ.variation, ‖step k x‖ ≤ C := by
    intro k
    filter_upwards [hsupport] with x hx
    obtain ⟨i, hi, hxi⟩ := hcover k x hx
    rw [show step k x = c k i from partitionCoefficient_eq (hdisj k) hi hxi]
    exact norm_chordCoefficient_le (hC k i (Finset.mem_range.1 hi))
  have hlim : ∀ᵐ x ∂μ.variation, Tendsto (fun k => step k x) atTop
      (𝓝 (chordCoefficient F (Function.leftLim z x) (z x))) := by
    filter_upwards [hsupport] with x hx
    choose i hi hxi using fun k => hcover k x hx
    have hi' : ∀ k, i k < n k := fun k => Finset.mem_range.1 (hi k)
    obtain ⟨hl, hr⟩ := partition_endpoints_tendsto hi' hxi hmesh hδ
    have hzl : Tendsto (fun k => z (t k (i k))) atTop (𝓝 (Function.leftLim z x)) :=
      (hz.tendsto_leftLim x).comp (tendsto_nhdsWithin_iff.2
        ⟨hl, Eventually.of_forall (fun k => (hxi k).1)⟩)
    have hzr : Tendsto (fun k => z (t k (i k + 1))) atTop (𝓝 (z x)) :=
      (hright x (Ioc_subset_Icc_self hx)).tendsto.comp (tendsto_nhdsWithin_iff.2
        ⟨hr, Eventually.of_forall (fun k => (hxi k).2)⟩)
    have he := tendsto_chordCoefficient hzl hzr
      (fun k => hF k _ (hi' k)) (hFjump x hx) ⟨C, fun k => hC k _ (hi' k)⟩
    exact he.congr' (Eventually.of_forall (fun k => (partitionCoefficient_eq (hdisj k) (hi k) (hxi k)).symm))
  have hDCT := VectorMeasure.tendsto_integral_filter_of_norm_le_const
    (μ := μ) (B := derivativePairing) (Eventually.of_forall (fun k => (hstepi k).aestronglyMeasurable))
    ⟨C, Eventually.of_forall hnorm⟩ hlim
  have hvalue : ∀ k, (∫ᵛ x, step k x ∂[derivativePairing; μ]) = F (z b) - F (z a) := by
    intro k
    rw [show step k = partitionCoefficient (Finset.range (n k)) (A k) (c k) from rfl,
      integral_partitionCoefficient derivativePairing _ _ _ (fun _ _ => measurableSet_Ioc)]
    have hcell : ∀ i ∈ Finset.range (n k), μ (A k i) = z (t k (i + 1)) - z (t k i) := by
      intro i hi
      have him : i < n k := Finset.mem_range.1 hi
      have hmem : ∀ j, j ≤ n k → t k j ∈ Icc a b := by
        intro j hj
        exact ⟨by rw [← ha k]; exact ht k (Nat.zero_le _), by rw [← hb k]; exact ht k hj⟩
      have hisub : A k i ⊆ Ioc a b := Ioc_subset_Ioc (hmem i him.le).1
        (hmem _ (Nat.succ_le_of_lt him)).2
      rw [show μ (A k i) = hz.vectorMeasure (A k i) from by
        exact (VectorMeasure.restrict_apply _ measurableSet_Ioc measurableSet_Ioc).trans
          (congrArg hz.vectorMeasure (inter_eq_left.2 hisub)), hz.vectorMeasure_Ioc (ht k (Nat.le_succ i)),
        (hright _ (hmem _ (Nat.succ_le_of_lt him))).rightLim_eq,
        (hright _ (hmem _ him.le)).rightLim_eq]
    calc
      _ = ∑ i ∈ Finset.range (n k), (F (z (t k (i + 1))) - F (z (t k i))) := by
        apply Finset.sum_congr rfl
        intro i hi
        change c k i (μ (A k i)) = _
        rw [hcell i hi]
        exact chordCoefficient_apply_sub (hF k i (Finset.mem_range.1 hi))
      _ = _ := by simpa only [ha k, hb k] using
        Finset.sum_range_sub (fun j => F (z (t k j))) (n k)
  exact tendsto_nhds_unique hDCT (by simpa only [hvalue] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => F (z b) - F (z a)) atTop (𝓝 _)))

end
end krylov.ContinuumBV
