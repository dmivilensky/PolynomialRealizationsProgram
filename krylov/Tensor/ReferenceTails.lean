import krylov.Tensor.ReferenceLowerBound

/-!
Article: main_krylov, eq:tensor-product and prop:Fcycle(i), true CG anchor geometry.
Use: bound the corrected model and fresh defect by the actual initial and
first remaining errors, retaining the source's constants.
Source: actual CG orthogonal step sums and exact Pythagoras.
-/

namespace krylov.Tensor
noncomputable section
open krylov.Reference krylov.Variation Matrix Finset
open scoped InnerProductSpace BigOperators Matrix.Norms.L2Operator
variable {n : ℕ}

/-- The actual final-anchor displacement from a true reference segment midpoint.
Article: main_krylov, eq:tensor-product, zeta_i. -/
def referenceAnchorDrift (A : Matrix (Fin n) (Fin n) ℝ)
    (g : EuclideanSpace ℝ (Fin n)) (i : ℕ) : EuclideanSpace ℝ (Fin n) :=
  (1 / 2 : ℝ) • canonicalCGStep A g i + remainingTail A g i

/-- An actual unit reference step extracts its actual step length from precisely the earlier tails.
Article: main_krylov, prop:Fcycle(i).
Proof: expand the genuine terminal displacement as its true orthogonal CG step sum. -/
theorem reference_unit_tail_pair (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (i : Fin (referenceAtomCount A hA g))
    (l : ℕ) (hl : l < referenceAtomCount A hA g) :
    inner ℝ (canonicalCGUnitStep A g i.val) (remainingTail A g l) =
      if l < i.val then ‖canonicalCGStep A g i.val‖ else 0 := by
  rw [remainingTail_eq_sum A hA g l hl, inner_sum]
  have hp (j : ℕ) (hj : j ∈ Ico (l+1) (referenceAtomCount A hA g)) :=
    canonical_step_unit_pair A hA g i ⟨j, (mem_Ico.mp hj).2⟩
  by_cases hi : l < i.val
  · rw [ite_eq_left hi, sum_eq_single i.val]
    · simpa only [ite_true] using hp i.val (mem_Ico.mpr ⟨by omega, i.isLt⟩)
    · intro j hj hji
      have hij : i ≠ (⟨j, (mem_Ico.mp hj).2⟩ : Fin (referenceAtomCount A hA g)) := by
        intro heq
        exact hji (congrArg Fin.val heq).symm
      simpa only [ite_eq_right hij] using hp j hj
    · intro hn
      exact (hn (mem_Ico.mpr ⟨by omega, i.isLt⟩)).elim
  · rw [ite_eq_right hi]
    apply sum_eq_zero
    intro j hj
    have hij : i ≠ (⟨j, (mem_Ico.mp hj).2⟩ : Fin (referenceAtomCount A hA g)) := by
      intro heq
      have hjv := congrArg Fin.val heq
      change i.val = j at hjv
      have hjl := (mem_Ico.mp hj).1
      omega
    simpa only [ite_eq_right hij] using hp j hj

/-- Every actual midpoint-to-final-anchor vector is bounded by its true pre-search error.
Article: main_krylov, prop:Fcycle(i).
Proof: its orthogonal step coefficient is one-half and its remaining error coefficient is one. -/
theorem reference_anchor_drift_le (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (i : ℕ) :
    ‖referenceAnchorDrift A g i‖ ≤ ‖cgCanonicalError A g i‖ := by
  have ho : inner ℝ (canonicalCGStep A g i) (remainingTail A g i) = 0 := by
    change inner ℝ (canonicalCGStep A g i) (-cgCanonicalError A g (i+1)) = 0
    rw [inner_neg_right, canonicalCGStep_postsearch_orth A hA, neg_zero]
  have hd := cgEnergy_drop A hA g i
  rw [cgEnergy_eq_norm_sq A hA] at hd
  have hn := norm_add_sq_real ((1/2 : ℝ) • canonicalCGStep A g i) (remainingTail A g i)
  rw [inner_smul_left, conj_trivial, ho, mul_zero, mul_zero, add_zero,
    norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0:ℝ)<1/2), remainingTail_norm] at hn
  change ‖(1/2 : ℝ) • canonicalCGStep A g i + remainingTail A g i‖ ≤ _
  nlinarith only [hn, hd, sq_nonneg ‖canonicalCGStep A g i‖,
    norm_nonneg ((1/2 : ℝ) • canonicalCGStep A g i + remainingTail A g i),
    norm_nonneg (cgCanonicalError A g i)]

/-- The final genuine reference tail vanishes exactly at actual CG termination.
Article: main_krylov, eq:tensor-product. -/
theorem reference_last_tail_zero (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hN : 0 < referenceAtomCount A hA g) :
    remainingTail A g (referenceAtomCount A hA g - 1) = 0 := by
  have hi : referenceAtomCount A hA g - 1 + 1 = referenceAtomCount A hA g := by omega
  simp only [remainingTail, cgCanonicalError, hi, cg_terminates A hA g, map_zero, neg_zero]

/-- Subtracting the last true midpoint drift cannot enlarge any earlier anchor drift.
Article: main_krylov, prop:Fcycle(i), the fresh tensor argument.
Proof: its component along the last actual step drops from one to one-half;
all other components remain orthogonal to that actual step. -/
theorem reference_anchor_difference_le (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hN : 0 < referenceAtomCount A hA g)
    (i : Fin (referenceAtomCount A hA g)) :
    ‖referenceAnchorDrift A g i.val - referenceAnchorDrift A g (referenceAtomCount A hA g - 1)‖ ≤
      ‖cgCanonicalError A g i.val‖ := by
  let j := referenceAtomCount A hA g - 1
  have hj : j < referenceAtomCount A hA g := by dsimp [j]; omega
  change ‖referenceAnchorDrift A g i.val - referenceAnchorDrift A g j‖ ≤ _
  by_cases hij : i.val = j
  · simp only [hij, sub_self, norm_zero, norm_nonneg]
  · have hij' : i.val < j := by omega
    have ho := canonicalCGStep_orth A hA g i.val j hij'
      (fun k hk => cg_nonstagnation A hA g k (hk.trans hj))
    have hp := reference_unit_tail_pair A hA g ⟨j, hj⟩ i.val i.isLt
    rw [ite_eq_left hij'] at hp
    have hs : canonicalCGStep A g j = ‖canonicalCGStep A g j‖ • canonicalCGUnitStep A g j :=
      (NormedSpace.norm_smul_normalize _).symm
    have hpair : inner ℝ (referenceAnchorDrift A g i.val) (canonicalCGStep A g j) =
        ‖canonicalCGStep A g j‖ ^ 2 := by
      rw [referenceAnchorDrift, inner_add_left, inner_smul_left, conj_trivial, ho, mul_zero,
        zero_add, real_inner_comm]
      conv_lhs => rw [hs]
      rw [inner_smul_left, conj_trivial, hp]
      ring
    have hlast : referenceAnchorDrift A g j = (1/2 : ℝ) • canonicalCGStep A g j := by
      rw [referenceAnchorDrift, reference_last_tail_zero A hA g hN, add_zero]
    have hn := norm_sub_sq_real (referenceAnchorDrift A g i.val) (referenceAnchorDrift A g j)
    rw [hlast, inner_smul_right, hpair, norm_smul, Real.norm_eq_abs,
      abs_of_pos (by norm_num : (0:ℝ)<1/2)] at hn
    have hb := reference_anchor_drift_le A hA g i.val
    have hsquare : ‖referenceAnchorDrift A g i.val - referenceAnchorDrift A g j‖ ^ 2 ≤
        ‖referenceAnchorDrift A g i.val‖ ^ 2 := by
      rw [hlast]
      nlinarith only [hn, sq_nonneg ‖canonicalCGStep A g j‖]
    have hnorm : ‖referenceAnchorDrift A g i.val - referenceAnchorDrift A g j‖ ≤
        ‖referenceAnchorDrift A g i.val‖ := by
      nlinarith only [hsquare, norm_nonneg (referenceAnchorDrift A g i.val),
        norm_nonneg (referenceAnchorDrift A g i.val-referenceAnchorDrift A g j)]
    exact hnorm.trans hb

end
end krylov.Tensor
