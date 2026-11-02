import krylov.ContinuumBV.TaylorSums
import krylov.ContinuumBV.MeasureSums
import Mathlib.MeasureTheory.VectorMeasure.BoundedVariation
import Mathlib.Order.Interval.Set.Union

/-!
Article: main_krylov, apC:lem:fund, continuous nonlinear BV chain rule.
Use: prove the chain identity from actual refining time partitions, derivative
estimates and finite variation. Both limits are proved: Taylor sums converge
to the potential increment, and the same sums converge to the vector integral.
No chain identity or integral-limit conclusion is an input hypothesis.

The hypotheses explicitly record a sequence of partitions and its vanishing
derivative oscillation. Constructing these from compact C¹ regularity is a
separate specialization. Continuous paths may carry singular continuous mass.
Source: Taylor remainder, finite measure sums and the BV Stieltjes measure.
-/

namespace krylov.ContinuumBV
noncomputable section
open Set Filter MeasureTheory
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Canonical pairing of a continuous linear derivative with a state increment. -/
def derivativePairing : (E →L[ℝ] ℝ) →L[ℝ] E →L[ℝ] ℝ :=
  (ContinuousLinearMap.apply ℝ ℝ).flip

/-- Continuous BV chain rule from genuine partitions with vanishing derivative
oscillation. Singular continuous variation is included in the actual vector
integral; no Lebesgue-density representation of dz is assumed. -/
theorem continuous_chain_of_partitions {z : ℝ → E} (hz : BoundedVariationOn z univ)
    (hzc : Continuous z) {F : E → ℝ} {D : E → E →L[ℝ] ℝ}
    {a b : ℝ} (t : ℕ → ℕ → ℝ) (n : ℕ → ℕ) (ε : ℕ → ℝ)
    (ht : ∀ k, Monotone (t k)) (ha : ∀ k, t k 0 = a) (hb : ∀ k, t k (n k) = b)
    (hF : ∀ k i, i < n k → ∀ w ∈ segment ℝ (z (t k i)) (z (t k (i + 1))),
      HasFDerivAt F (D w) w)
    (hD : ∀ k i, i < n k → ∀ w ∈ segment ℝ (z (t k i)) (z (t k (i + 1))),
      ‖D w - D (z (t k i))‖ ≤ ε k)
    (hpath : ∀ k i, i < n k → ∀ x ∈ Ioc (t k i) (t k (i + 1)),
      ‖D (z (t k i)) - D (z x)‖ ≤ ε k)
    (hε : ∀ k, 0 ≤ ε k) (hεlim : Tendsto ε atTop (𝓝 0))
    (hint : (hz.vectorMeasure.restrict (Ioc a b)).Integrable (fun x => D (z x))) :
    (∫ᵛ x in Ioc a b, D (z x) ∂[derivativePairing; hz.vectorMeasure]) = F (z b) - F (z a) := by
  let μ := hz.vectorMeasure.restrict (Ioc a b)
  let c : ℝ → E →L[ℝ] ℝ := fun x => D (z x)
  have hμvar : μ.variation = hz.vectorMeasure.variation.restrict (Ioc a b) :=
    VectorMeasure.variation_restrict measurableSet_Ioc
  have hTaylor := derivativeSum_tendsto (fun k i => z (t k i)) n
    (fun k => congrArg z (ha k)) (fun k => congrArg z (hb k)) hF hD hε hεlim
    (fun k => partition_variation_le hz (ht k) (fun _ => mem_univ _) (n k))
  have hbound : ∀ k,
      ‖derivativeSum D (fun i => z (t k i)) (n k) - (∫ᵛ x, c x ∂[derivativePairing; μ])‖ ≤
        ε k * ‖(derivativePairing : (E →L[ℝ] ℝ) →L[ℝ] E →L[ℝ] ℝ)‖ *
          μ.variation.real univ := by
    intro k
    let A : ℕ → Set ℝ := fun i => Ioc (t k i) (t k (i + 1))
    have hA : ∀ i ∈ Finset.range (n k), MeasurableSet (A i) := fun _ _ => measurableSet_Ioc
    have hdisj : (Finset.range (n k) : Set ℕ).PairwiseDisjoint A := by
      intro i _hi j _hj hij
      rcases lt_or_gt_of_ne hij with hij | hji
      · exact Ioc_disjoint_Ioc_of_le (ht k (Nat.succ_le_of_lt hij))
      · exact (Ioc_disjoint_Ioc_of_le (ht k (Nat.succ_le_of_lt hji))).symm
    have hcover : ∀ᵐ x ∂μ.variation, ∃ i ∈ Finset.range (n k), x ∈ A i := by
      rw [hμvar]
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      have hx' : x ∈ Ioc (t k 0) (t k (n k)) := by simpa only [ha k, hb k] using hx
      obtain ⟨i, hi, hxi⟩ := (show ∃ i, ∃ hi : i ∈ Finset.range (n k),
          x ∈ Ioc (t k i) (t k (i + 1)) from by
        simpa only [mem_iUnion] using Ioc_subset_biUnion_Ioc (n k) (t k) hx')
      exact ⟨i, hi, hxi⟩
    have hcell : ∀ i ∈ Finset.range (n k), μ (A i) = z (t k (i + 1)) - z (t k i) := by
      intro i hi
      have hisub : A i ⊆ Ioc a b := by
        intro x hx
        have hai : a ≤ t k i := by rw [← ha k]; exact ht k (Nat.zero_le _)
        have hib : t k (i + 1) ≤ b := by
          rw [← hb k]
          exact ht k (Nat.succ_le_of_lt (Finset.mem_range.1 hi))
        exact ⟨hai.trans_lt hx.1, hx.2.trans hib⟩
      change (hz.vectorMeasure.restrict (Ioc a b)) (A i) = _
      rw [VectorMeasure.restrict_apply _ measurableSet_Ioc (hA i hi), inter_eq_left.2 hisub]
      rw [hz.vectorMeasure_Ioc (ht k (Nat.le_succ i)),
        hzc.continuousAt.continuousWithinAt.rightLim_eq,
        hzc.continuousAt.continuousWithinAt.rightLim_eq]
    have he := norm_tagged_sum_sub_integral_le
      (μ := μ) derivativePairing (Finset.range (n k)) A (fun i => D (z (t k i)))
      hA hdisj hcover hint (fun i hi => hpath k i (Finset.mem_range.1 hi))
    convert he using 1
    congr 2
    unfold derivativeSum
    apply Finset.sum_congr rfl
    intro i hi
    rw [hcell i hi]
    rfl
  have hIntegral : Tendsto (fun k => derivativeSum D (fun i => z (t k i)) (n k)) atTop
      (𝓝 (∫ᵛ x, c x ∂[derivativePairing; μ])) := by
    apply tendsto_iff_norm_sub_tendsto_zero.2
    apply squeeze_zero (fun _ => norm_nonneg _) hbound
    simpa only [zero_mul] using
      ((hεlim.mul_const ‖(derivativePairing : (E →L[ℝ] ℝ) →L[ℝ] E →L[ℝ] ℝ)‖).mul_const
        (μ.variation.real univ))
  exact tendsto_nhds_unique hIntegral hTaylor

end
end krylov.ContinuumBV
