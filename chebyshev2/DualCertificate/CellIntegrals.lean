import chebyshev2.DualCertificate.Cells
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
Article: chebyshev2, Lemma 16.
Exact finite cell decomposition, insensitive to the selected values at shared endpoints.
Use: `chebyshev2.DualCertificate.Cells.weighted_integral` feeds
`chebyshev2.DualCertificate.Data.price_cost_cells` (price cost cells).
Proof chain: `chebyshev2.DualCertificate.Data.uniform_finite_lower_bound` — chebyshev2,
Theorem 3.6; admissible certificates imply continuum, finite-fiber and gain bounds.
-/
namespace chebyshev2.DualCertificate.Cells
noncomputable section
open Set MeasureTheory Filter
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable (P : Cells)

/--
The stated quantitative bound `P.value =ᵐ[volume] fun t => ∑ i,(Icc (P.lo i:ℝ) (P.hi
i:ℝ)).indicator (P.affine i) t`.

Use: `chebyshev2.DualCertificate.Cells.weighted_integral` uses this identity to establish
the precise assertion is `(∫ t in Icc (0:ℝ) 1,w t*P.value t)= ∑ i,∫ t in Icc (P.lo i:ℝ) (P.hi
i:ℝ),w t*P.affine i t`.

Article: chebyshev2, Theorem E.1 via
`chebyshev2.DualCertificate.Data.packed_value_tendsto`.

Proof: Separate `t∈Icc (0:ℝ) 1` from its negation; prove the goal under each of these mutually
exclusive hypotheses. Intersect the eventual or almost-everywhere hypotheses, then prove the
asserted relation at an arbitrary point in that intersection.
-/
theorem value_ae_cells : P.value =ᵐ[volume]
    fun t => ∑ i,(Icc (P.lo i:ℝ) (P.hi i:ℝ)).indicator (P.affine i) t := by
  -- Separate `t∈Icc (0:ℝ) 1` from its negation; prove the goal under each of these mutually
  -- exclusive hypotheses.
  have he : ∀ᵐ t : ℝ,t∉(P.endpoints:Set ℝ) :=
    (measure_eq_zero_iff_ae_notMem).mp (P.endpoints.measure_zero volume)
  filter_upwards [he] with t ht
  by_cases hin : t∈Icc (0:ℝ) 1
  · let i := P.index t hin
    have hi := P.index_mem hin
    have hti : t∈Ioo (P.lo i:ℝ) (P.hi i:ℝ) := by
      refine ⟨lt_of_le_of_ne hi.1 ?_,lt_of_le_of_ne hi.2 ?_⟩
      · exact fun h => ht (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,h⟩))
      · exact fun h => ht (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,h.symm⟩))
    rw [P.value_on_interior hti,Finset.sum_eq_single i]
    · exact (indicator_of_mem hi _).symm
    · intro j _ hji
      apply indicator_of_notMem
      intro hj
      exact hji (P.interior_unique hti hj)
    · exact fun h => False.elim (h (Finset.mem_univ _))
  · rw [value,dite_eq_right hin]
    symm
    apply Finset.sum_eq_zero
    intro i _
    apply indicator_of_notMem
    exact fun hi => hin (P.cell_inside i hi)

/--
The precise assertion is `(∫ t in Icc (0:ℝ) 1,w t*P.value t)= ∑ i,∫ t in Icc (P.lo i:ℝ) (P.hi
i:ℝ),w t*P.affine i t`.

Use: `chebyshev2.DualCertificate.Data.price_cost_cells` rewrites with this identity to
establish the identity stated in that declaration.

Article: chebyshev2, Theorem E.1 via
`chebyshev2.DualCertificate.Data.packed_value_tendsto`.

Proof: Separate `t∈Icc (0:ℝ) 1` from its negation; prove the goal under each of these mutually
exclusive hypotheses. Intersect the eventual or almost-everywhere hypotheses, then prove the
asserted relation at an arbitrary point in that intersection. Identify the summands/integrands
on their required domain before replacing the sum or integral.
-/
theorem weighted_integral {w : ℝ → ℝ} (hw : ContinuousOn w (Icc (0:ℝ) 1)) :
    (∫ t in Icc (0:ℝ) 1,w t*P.value t)=
      ∑ i,∫ t in Icc (P.lo i:ℝ) (P.hi i:ℝ),w t*P.affine i t := by
  -- Establish hcell as the integrability justification for the later integral estimates or
  -- changes of order.
  have hcell (i : Fin P.count) : Integrable
      ((Icc (P.lo i:ℝ) (P.hi i:ℝ)).indicator (fun t => w t*P.affine i t)) := by
    apply (integrable_indicator_iff measurableSet_Icc).mpr
    exact ((hw.mono (P.cell_inside i)).mul
      ((by unfold affine;fun_prop : Continuous (P.affine i)).continuousOn)).integrableOn_compact
        (μ := volume) isCompact_Icc
  have he : (Icc (0:ℝ) 1).indicator (fun t => w t*P.value t)=ᵐ[volume]
      fun t => ∑ i,(Icc (P.lo i:ℝ) (P.hi i:ℝ)).indicator (fun t => w t*P.affine i t) t := by
    filter_upwards [P.value_ae_cells] with t ht
    by_cases hin : t∈Icc (0:ℝ) 1
    · rw [indicator_of_mem hin,ht,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : t∈Icc (P.lo i:ℝ) (P.hi i:ℝ)
      · rw [indicator_of_mem hi,indicator_of_mem hi]
      · rw [indicator_of_notMem hi,indicator_of_notMem hi,mul_zero]
    · rw [indicator_of_notMem hin]
      symm
      apply Finset.sum_eq_zero
      intro i _
      exact indicator_of_notMem (fun hi => hin (P.cell_inside i hi)) _
  rw [← integral_indicator measurableSet_Icc,integral_congr_ae he,
    integral_finsetSum Finset.univ (fun i _ => hcell i)]
  simp only [integral_indicator measurableSet_Icc]

end
end chebyshev2.DualCertificate.Cells
