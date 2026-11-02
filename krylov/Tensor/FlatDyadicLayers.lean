import krylov.Tensor.FlatDyadicExpansion

/-!
Article: main_krylov, apG:flat, genuine dyadic layer nuclear-cost estimates.
Use: control every actual pair of dyadic levels using their real nested
supports, true indicator norms and genuine Bessel/Cauchy restriction bounds.
Source: the dyadic prefix construction and standard orthogonal partition estimates.
-/

namespace krylov.Tensor
noncomputable section
open Finset
open scoped BigOperators InnerProductSpace
variable {ι κ E : Type*} [Fintype κ] [DecidableEq ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A fine support meets at most one actual disjoint coarse block, so its true restricted-vector costs sum to at most its own norm.
Article: main_krylov, apG:flat, the unique-coarse-intersection estimate. -/
theorem sum_norm_flagComponent_inter_le (e : ι → E) (A : Finset ι) (B : κ → Finset ι)
    (hB : Pairwise (fun j k => Disjoint (B j) (B k)))
    (hsub : ∀ j, (A ∩ B j).Nonempty → A ⊆ B j) (u : E) :
    ∑ j : κ, ‖flagComponent e (A ∩ B j) u‖ ≤ ‖flagComponent e A u‖ := by
  classical
  by_cases hex : ∃ j, (A ∩ B j).Nonempty
  · obtain ⟨j, hj⟩ := hex
    have hA : A ∩ B j = A := inter_eq_left.mpr (hsub j hj)
    rw [Finset.sum_eq_single j]
    · rw [hA]
    · intro k _ hkj
      have hzero : A ∩ B k = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro a ha
        have ha' := Finset.mem_inter.mp ha
        exact Finset.disjoint_left.mp (hB hkj) ha'.2 (hsub j hj ha'.1)
      simp only [hzero, flagComponent, sum_empty, norm_zero]
    · intro hj'
      exact (hj' (mem_univ j)).elim
  · have hz j : A ∩ B j = ∅ := Finset.not_nonempty_iff_eq_empty.mp (fun h => hex ⟨j, h⟩)
    simp only [hz, flagComponent, sum_empty, norm_zero, sum_const_zero, norm_nonneg]

variable {N L : ℕ}

/-- The real dyadic left-block vector has at most the square root of its actual dyadic length as its norm.
Article: main_krylov, apG:flat, actual rank-one factor norms. -/
theorem dyadicLeftVector_norm_le (e : Fin N → E) (he : Orthonormal ℝ e) (p : DyadicPrefixIndex L) :
    ‖dyadicLeftVector e p‖ ≤ Real.sqrt (2 ^ p.1.val : ℕ) := by
  rw [dyadicLeftVector, norm_orthonormal_sum e he]
  exact Real.sqrt_le_sqrt (by exact_mod_cast dyadicHalf_card_le N p.1.val p.2.val false)

/-- The actual pairwise dyadic rank-one cost at two ordered levels obeys the genuine paper layer bound.
Article: main_krylov, apG:flat, layer-pair Cauchy--Schwarz estimate.
Proof: the actual finer right blocks are disjoint and each meets at most one
actual coarser right block. Restrict the true output vector, apply the proved
orthogonal Cauchy bound, and use the true dyadic indicator-vector norms. -/
theorem flatDyadic_layer_cost_le (e : Fin N → E) (he : Orthonormal ℝ e)
    (k l : Fin L) (hkl : k.val ≤ l.val) (u : E) :
    ∑ r : Fin (2 ^ (L - (k.val + 1))), ∑ s : Fin (2 ^ (L - (l.val + 1))),
      ‖flagComponent e (dyadicHalf N k.val r.val true ∩ dyadicHalf N l.val s.val true) u‖ *
        ‖dyadicLeftVector e (⟨k, r⟩ : DyadicPrefixIndex L)‖ *
        ‖dyadicLeftVector e (⟨l, s⟩ : DyadicPrefixIndex L)‖ ≤
      Real.sqrt (2 ^ k.val : ℕ) * Real.sqrt (2 ^ l.val : ℕ) *
        Real.sqrt (2 ^ (L - (k.val + 1)) : ℕ) * ‖u‖ := by
  have hdisj (j : Fin L) : Pairwise (fun r s : Fin (2 ^ (L - (j.val + 1))) =>
      Disjoint (dyadicHalf N j.val r.val true) (dyadicHalf N j.val s.val true)) := by
    intro r s hrs
    exact dyadicHalf_disjoint N j.val r.val s.val true (fun h => hrs (Fin.ext h))
  have hrow (r : Fin (2 ^ (L - (k.val + 1)))) : ∑ s : Fin (2 ^ (L - (l.val + 1))),
      ‖flagComponent e (dyadicHalf N k.val r.val true ∩ dyadicHalf N l.val s.val true) u‖ ≤
        ‖flagComponent e (dyadicHalf N k.val r.val true) u‖ :=
    sum_norm_flagComponent_inter_le e _ _ (hdisj l)
      (fun s hs => dyadicHalf_subset_of_inter_le N k.val l.val r.val s.val true hkl hs) u
  have hsum := sum_norm_flagComponent_le e he (fun r : Fin (2 ^ (L - (k.val + 1))) =>
    dyadicHalf N k.val r.val true) (hdisj k) u
  simp only [Fintype.card_fin] at hsum
  calc
    _ ≤ ∑ r : Fin (2 ^ (L - (k.val + 1))), ∑ s : Fin (2 ^ (L - (l.val + 1))),
        ‖flagComponent e (dyadicHalf N k.val r.val true ∩ dyadicHalf N l.val s.val true) u‖ *
          Real.sqrt (2 ^ k.val : ℕ) * Real.sqrt (2 ^ l.val : ℕ) := by
      apply sum_le_sum
      intro r _
      apply sum_le_sum
      intro s _
      exact mul_le_mul (mul_le_mul_of_nonneg_left (dyadicLeftVector_norm_le e he ⟨k, r⟩) (norm_nonneg _))
        (dyadicLeftVector_norm_le e he ⟨l, s⟩) (norm_nonneg _) (by positivity)
    _ = Real.sqrt (2 ^ k.val : ℕ) * Real.sqrt (2 ^ l.val : ℕ) *
        ∑ r : Fin (2 ^ (L - (k.val + 1))), ∑ s : Fin (2 ^ (L - (l.val + 1))),
          ‖flagComponent e (dyadicHalf N k.val r.val true ∩ dyadicHalf N l.val s.val true) u‖ := by
      simp only [mul_sum]
      congr 2
      funext r
      congr 1
      funext s
      ring
    _ ≤ Real.sqrt (2 ^ k.val : ℕ) * Real.sqrt (2 ^ l.val : ℕ) *
        ∑ r : Fin (2 ^ (L - (k.val + 1))), ‖flagComponent e (dyadicHalf N k.val r.val true) u‖ := by
      exact mul_le_mul_of_nonneg_left (sum_le_sum (fun r _ => hrow r)) (by positivity)
    _ ≤ _ := (mul_le_mul_of_nonneg_left hsum (by positivity)).trans_eq (by ring)

end
end krylov.Tensor
