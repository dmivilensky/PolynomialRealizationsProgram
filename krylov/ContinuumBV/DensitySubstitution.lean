import krylov.ContinuumBV.BochnerSums
import krylov.ContinuumBV.ChainPartitions
import krylov.ContinuumBV.EqualGrid
import Mathlib.Topology.UniformSpace.HeineCantor

/-!
Article: main_krylov, apC:lem:fund, physical splitting of the vector integral.
Use: identify a continuous-coefficient vector-measure integral with two
ordinary density integrals from the actual interval increments of the state.
The proof compares the same finite tagged sums against all three integrals.
Source: compact uniform continuity, equal grids, vector and Bochner sum bounds.
-/

namespace krylov.ContinuumBV
noncomputable section
open Set Filter MeasureTheory
open scoped Topology

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

omit [CompleteSpace V] in
/-- Continuous coefficients on a compact interval admit genuine equal grids
with any prescribed cell oscillation. -/
theorem exists_coefficient_grid {a b : ℝ} (hab : a ≤ b) {c : ℝ → V →L[ℝ] ℝ}
    (hc : ContinuousOn c (Icc a b)) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, 0 < N ∧ ∀ i < N, ∀ x ∈ Ioc (equalGrid a b N i) (equalGrid a b N (i + 1)),
      ‖c (equalGrid a b N i) - c x‖ ≤ ε := by
  obtain ⟨δ, hδ, hosc⟩ := Metric.uniformContinuousOn_iff.1
    (isCompact_Icc.uniformContinuousOn_of_continuous hc) ε hε
  obtain ⟨N, hN, ht, _ha, _hb, hmem, hmesh⟩ := exists_equalGrid hab hδ
  refine ⟨N, hN, ?_⟩
  intro i hi x hx
  have hxmem : x ∈ Icc a b :=
    ⟨(hmem i).1.trans hx.1.le, hx.2.trans (hmem (i + 1)).2⟩
  have hd : dist (equalGrid a b N i) x < δ := by
    rw [dist_comm, Real.dist_eq, abs_of_nonneg (sub_nonneg.2 hx.1.le)]
    exact (sub_le_sub_right hx.2 _).trans_lt (hmesh i hi)
  simpa only [dist_eq_norm] using (hosc _ (hmem i) x hxmem hd).le

/-- The actual physical decomposition of a vector integral follows from its
interval increments. The measures may have arbitrary singular mass or atoms;
only the coefficient is required to be continuous on the physical window. -/
theorem integral_eq_two_density_integrals {a b : ℝ} (hab : a ≤ b)
    (ν : VectorMeasure ℝ V) [IsFiniteMeasure ν.variation]
    (μ₁ μ₂ : Measure ℝ) (h₁ h₂ : ℝ → V) {c : ℝ → V →L[ℝ] ℝ}
    (hc : ContinuousOn c (Icc a b))
    (hν : ∀ᵐ x ∂ν.variation, x ∈ Ioc a b)
    (hμ₁ : ∀ᵐ x ∂μ₁, x ∈ Ioc a b) (hμ₂ : ∀ᵐ x ∂μ₂, x ∈ Ioc a b)
    (hiν : ν.Integrable c) (hi₁ : Integrable h₁ μ₁) (hi₂ : Integrable h₂ μ₂)
    (hci₁ : Integrable (fun x => c x (h₁ x)) μ₁)
    (hci₂ : Integrable (fun x => c x (h₂ x)) μ₂)
    (hcell : ∀ u v, a ≤ u → u ≤ v → v ≤ b →
      ν (Ioc u v) = (∫ x in Ioc u v, h₁ x ∂μ₁) + (∫ x in Ioc u v, h₂ x ∂μ₂)) :
    (∫ᵛ x, c x ∂[derivativePairing; ν]) =
      (∫ x, c x (h₁ x) ∂μ₁) + (∫ x, c x (h₂ x) ∂μ₂) := by
  let ε : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  have hε : ∀ k, 0 < ε k := by intro k; dsimp [ε]; positivity
  have hεlim : Tendsto ε atTop (nhds 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  choose N hN hosc using fun k => exists_coefficient_grid hab hc (hε k)
  let A : ℕ → ℕ → Set ℝ := fun k i => Ioc (equalGrid a b (N k) i) (equalGrid a b (N k) (i + 1))
  let tag : ℕ → ℕ → V →L[ℝ] ℝ := fun k i => c (equalGrid a b (N k) i)
  let S : ℕ → ℝ := fun k => ∑ i ∈ Finset.range (N k), tag k i (ν (A k i))
  let S₁ : ℕ → ℝ := fun k => ∑ i ∈ Finset.range (N k), tag k i (∫ x in A k i, h₁ x ∂μ₁)
  let S₂ : ℕ → ℝ := fun k => ∑ i ∈ Finset.range (N k), tag k i (∫ x in A k i, h₂ x ∂μ₂)
  have hA : ∀ k i, MeasurableSet (A k i) := fun _ _ => measurableSet_Ioc
  have hdisj : ∀ k, (Finset.range (N k) : Set ℕ).PairwiseDisjoint (A k) := by
    intro k i _hi j _hj hij
    rcases lt_or_gt_of_ne hij with hij | hji
    · exact Ioc_disjoint_Ioc_of_le (equalGrid_mono hab _ (Nat.succ_le_of_lt hij))
    · exact (Ioc_disjoint_Ioc_of_le (equalGrid_mono hab _ (Nat.succ_le_of_lt hji))).symm
  have hcover : ∀ k x, x ∈ Ioc a b → ∃ i ∈ Finset.range (N k), x ∈ A k i := by
    intro k x hx
    have hx' : x ∈ Ioc (equalGrid a b (N k) 0) (equalGrid a b (N k) (N k)) := by
      simpa only [equalGrid_zero, equalGrid_end a b (hN k)] using hx
    obtain ⟨i, hi, hxi⟩ := (show ∃ i, ∃ hi : i ∈ Finset.range (N k),
        x ∈ Ioc (equalGrid a b (N k) i) (equalGrid a b (N k) (i + 1)) from by
      simpa only [mem_iUnion] using Ioc_subset_biUnion_Ioc (N k) (equalGrid a b (N k)) hx')
    exact ⟨i, hi, hxi⟩
  have hS : Tendsto S atTop (nhds (∫ᵛ x, c x ∂[derivativePairing; ν])) := by
    apply tendsto_iff_norm_sub_tendsto_zero.2
    have hbnd : ∀ k, ‖S k - (∫ᵛ x, c x ∂[derivativePairing; ν])‖ ≤
        ε k * ‖(derivativePairing : (V →L[ℝ] ℝ) →L[ℝ] V →L[ℝ] ℝ)‖ * ν.variation.real univ := by
      intro k
      exact norm_tagged_sum_sub_integral_le derivativePairing _ _ _
        (fun i _ => hA k i) (hdisj k) (hν.mono (fun _ hx => hcover k _ hx)) hiν
        (fun i hi => hosc k i (Finset.mem_range.1 hi))
    apply squeeze_zero (fun _ => norm_nonneg _) hbnd
    simpa only [zero_mul] using
      (hεlim.mul_const ‖(derivativePairing : (V →L[ℝ] ℝ) →L[ℝ] V →L[ℝ] ℝ)‖).mul_const
        (ν.variation.real univ)
  have hS₁ : Tendsto S₁ atTop (nhds (∫ x, c x (h₁ x) ∂μ₁)) := by
    apply tendsto_iff_norm_sub_tendsto_zero.2
    have hbnd : ∀ k, ‖S₁ k - (∫ x, c x (h₁ x) ∂μ₁)‖ ≤ ε k * ∫ x, ‖h₁ x‖ ∂μ₁ := by
      intro k
      exact norm_density_tagged_sum_sub_integral_le hi₁ _ _ _
        (fun i _ => hA k i) (hdisj k) (hμ₁.mono (fun _ hx => hcover k _ hx)) hci₁
        (fun i hi => hosc k i (Finset.mem_range.1 hi))
    apply squeeze_zero (fun _ => norm_nonneg _) hbnd
    simpa only [zero_mul] using hεlim.mul_const (∫ x, ‖h₁ x‖ ∂μ₁)
  have hS₂ : Tendsto S₂ atTop (nhds (∫ x, c x (h₂ x) ∂μ₂)) := by
    apply tendsto_iff_norm_sub_tendsto_zero.2
    have hbnd : ∀ k, ‖S₂ k - (∫ x, c x (h₂ x) ∂μ₂)‖ ≤ ε k * ∫ x, ‖h₂ x‖ ∂μ₂ := by
      intro k
      exact norm_density_tagged_sum_sub_integral_le hi₂ _ _ _
        (fun i _ => hA k i) (hdisj k) (hμ₂.mono (fun _ hx => hcover k _ hx)) hci₂
        (fun i hi => hosc k i (Finset.mem_range.1 hi))
    apply squeeze_zero (fun _ => norm_nonneg _) hbnd
    simpa only [zero_mul] using hεlim.mul_const (∫ x, ‖h₂ x‖ ∂μ₂)
  have hsum : S = fun k => S₁ k + S₂ k := by
    funext k
    dsimp [S, S₁, S₂]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hcell _ _ (equalGrid_mem hab (hN k) i).1
      (equalGrid_mono hab (N k) (Nat.le_succ i)) (equalGrid_mem hab (hN k) (i + 1)).2,
      map_add]
  rw [hsum] at hS
  exact tendsto_nhds_unique hS (hS₁.add hS₂)

end
end krylov.ContinuumBV
