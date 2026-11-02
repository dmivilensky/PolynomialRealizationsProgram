import krylov.Functions.NativeRFCFReference
import krylov.Correction.ReferenceRegularity
import Mathlib.Analysis.Normed.Group.Bounded

/-!
Article: main_krylov, prop:Fcycle(i), genuine quadratic model-metric geometry.
Use: derive the reference split one-half and a common positive reference
secant energy from actual CG nonstagnation on its original compact set.
Source: proved real CG search orthogonality and compact continuous minima.
-/

namespace krylov.Functions
noncomputable section
open Real Set Metric krylov.Methods krylov.Reference krylov.Correction
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Every genuine nonstagnating CG step is nonzero before normalization.
Article: main_krylov, prop:Fcycle(i), nondegenerate split denominator. -/
theorem referenceStep_ne_zero_of_prefix (Q : E →L[ℝ] E)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E, v ≠ 0 → 0 < inner ℝ v (Q v))
    (g : E) (i : ℕ) (hpre : ∀ j ≤ i, CG.gradient Q g j ≠ 0) :
    referenceStep Q g i ≠ 0 := by
  have hi := CG.invariant Q hQ hpos g i (fun j hj => hpre j hj.le)
  obtain ⟨hd, hl, _⟩ := CG.invariant_line_pos Q hpos g i hi (hpre i le_rfl)
  exact smul_ne_zero hl.ne' hd

/-- Actual nondegenerate compact CG references have a common positive energy for every retained step.
Article: main_krylov, prop:Fcycle(i), uniform actual split denominator.
Continuity is derived from the genuine rational CG recurrence. -/
theorem compact_reference_step_energy (Q : E →L[ℝ] E)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E, v ≠ 0 → 0 < inner ℝ v (Q v))
    (k : ℕ) (K : Set E) (hK : IsCompact K)
    (hpre : ∀ g ∈ K, ∀ i < k+1, CG.gradient Q g i ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ g ∈ K, ∀ i : Fin (k+1),
      c ≤ inner ℝ (Q (referenceStep Q g i.val)) (referenceStep Q g i.val) := by
  have hi (i : Fin (k+1)) : ∃ c : ℝ, 0 < c ∧ ∀ g ∈ K,
      c ≤ inner ℝ (Q (referenceStep Q g i.val)) (referenceStep Q g i.val) := by
    have hs : ContinuousOn (fun g : E => referenceStep Q g i.val) K := by
      intro g hg
      exact (referenceStep_analyticAt (fun _ : E => Q) (fun g : E => g) g
        analyticAt_const analyticAt_id hQ hpos i.val (fun j hj => hpre g hg j (hj.trans_lt i.isLt))).continuousAt.continuousWithinAt
    apply hK.exists_forall_le' ((Q.continuous.comp_continuousOn hs).inner hs)
    intro g hg
    rw [real_inner_comm]
    exact hpos _ (referenceStep_ne_zero_of_prefix Q hQ hpos g i.val
      (fun j hj => hpre g hg j (hj.trans_lt i.isLt)))
  choose c hc hbound using hi
  let c₀ := Finset.univ.inf' Finset.univ_nonempty c
  refine ⟨c₀, (Finset.lt_inf'_iff _).mpr (fun i _ => hc i), ?_⟩
  intro g hg i
  exact (Finset.inf'_le c (Finset.mem_univ i)).trans (hbound i g hg)

/-- Actual nonstagnating compact CG references have uniformly bounded retained physical steps.
Article: main_krylov, prop:Fcycle(i), the true finite reference source bound. -/
theorem compact_reference_step_norm (Q : E →L[ℝ] E)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E, v ≠ 0 → 0 < inner ℝ v (Q v))
    (k : ℕ) (K : Set E) (hK : IsCompact K)
    (hpre : ∀ g ∈ K, ∀ i < k+1, CG.gradient Q g i ≠ 0) :
    ∃ M : ℝ, 0 < M ∧ ∀ g ∈ K, ∀ i : Fin (k+1), ‖referenceStep Q g i.val‖ ≤ M := by
  have hi (i : Fin (k+1)) : ∃ M : ℝ, ∀ g ∈ K, ‖referenceStep Q g i.val‖ ≤ M := by
    apply hK.exists_bound_of_continuousOn
    intro g hg
    exact (referenceStep_analyticAt (fun _ : E => Q) (fun g : E => g) g
      analyticAt_const analyticAt_id hQ hpos i.val (fun j hj => hpre g hg j (hj.trans_lt i.isLt))).continuousAt.continuousWithinAt
  choose c hbound using hi
  let M := 1 + ∑ i : Fin (k+1), |c i|
  have hM : 0 < M := by dsimp only [M]; positivity
  refine ⟨M, hM, ?_⟩
  intro g hg i
  have hh : |c i| ≤ ∑ j : Fin (k+1), |c j| :=
    Finset.single_le_sum (fun j _ => abs_nonneg (c j)) (Finset.mem_univ i)
  exact (hbound i g hg).trans ((le_abs_self _).trans (hh.trans (by dsimp only [M]; linarith)))

/-- The actual quadratic reference point carries its true computed CG gradient.
Article: main_krylov, prop:Fcycle(i), reference endpoint dictionary. -/
theorem fcQuadraticReferencePoint_gradient (Q : E →L[ℝ] E) (u : E) (j : ℕ) :
    Q (fcQuadraticReferencePoint Q u j) = CG.gradient Q (Q u) j := by
  rw [fcQuadraticReferencePoint, map_add, CG.gradient_displacement]

/-- Every retained reference step is Q-orthogonal to the displacement from its endpoint to the final reference anchor.
Article: main_krylov, prop:Fcycle(i), the exact model-metric split one-half.
The assertion follows from genuine post-search residual orthogonality at
both endpoints, before any nonlinear split or value model is introduced. -/
theorem referenceStep_terminal_endpoint_orthogonal (Q : E →L[ℝ] E)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E, v ≠ 0 → 0 < inner ℝ v (Q v))
    (u : E) (k : ℕ) (hpre : ∀ j < k+1, CG.gradient Q (Q u) j ≠ 0)
    (i : Fin (k+1)) :
    inner ℝ (Q (referenceStep Q (Q u) i.val))
      (fcQuadraticReferencePoint Q u (k+1) - fcQuadraticReferencePoint Q u (i.val+1)) = 0 := by
  have hs := hQ (referenceStep Q (Q u) i.val)
    (fcQuadraticReferencePoint Q u (k+1) - fcQuadraticReferencePoint Q u (i.val+1))
  change inner ℝ (Q (referenceStep Q (Q u) i.val)) _ =
    inner ℝ (referenceStep Q (Q u) i.val) (Q _) at hs
  rw [hs, map_sub, fcQuadraticReferencePoint_gradient, fcQuadraticReferencePoint_gradient,
    inner_sub_right,
    referenceStep_postsearch_orth Q hQ hpos (Q u) k (fun j hj => hpre j (by omega)) (by omega),
    referenceStep_postsearch_orth Q hQ hpos (Q u) i.val (fun j hj => hpre j (hj.trans_lt i.isLt)) le_rfl,
    sub_self]

end
end krylov.Functions
