import krylov.Methods.Windows

/-!
Article: main_krylov, alg:fc, repeated latest-model corrections.
Use: implement a fixed finite number of actual adaptive correction queries;
each coefficient solve uses its genuinely observed new gradient.
Source: the source article's RFC_k rule with a single fixed augmented model.
-/

namespace krylov.Methods
noncomputable section
open Matrix krylov.Reference
open scoped InnerProductSpace BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The actual repeated fixed-model correction decision tree.
Use: each subsequent right-hand side is computed only after observing its preceding correction gradient.
Article: main_krylov, alg:fc, repeat k_c times with the same H. -/
def repeatedModelTree (s : ι → E) (H : Matrix ι ι ℝ) : ℕ → E → CorrectionTree E
  | 0, _ => .done
  | c+1, g => .query (combine s (modelCoefficients s H g)) (repeatedModelTree s H c)

/-- Every actual repeated correction is zero if the projected gradient is zero.
Use: the genuine RFC_k correction tree preserves the quadratic reference for every finite k.
Article: main_krylov, lem:consistent(a), all repeated corrections vanish.
Proof: the computed coefficient vector itself is zero; querying its zero
physical combination preserves the actual gradient and the next right-hand side. -/
theorem repeatedModelTree_zero (s : ι → E) (H : Matrix ι ι ℝ) (B : E →L[ℝ] E)
    (g : E) (hg : coordinates s g=0) (c : ℕ) : ZeroCorrections (repeatedModelTree s H c g) B g := by
  induction c with
  | zero => trivial
  | succ c ih =>
    have hw := modelCoefficients_zero s H g hg
    have hs : combine s (modelCoefficients s H g)=0 := by
      simp only [hw, combine, Pi.zero_apply, zero_smul, Finset.sum_const_zero]
    change _=0 ∧ _
    exact ⟨hs, by simpa only [hs, map_zero, add_zero] using ih⟩

/-- Pairwise observed-vector orthogonality annihilates the actual window right-hand side.
Use: connect list-based actual transcripts to the finite coefficient correction model.
Article: main_krylov, lem:consistent(a), Uᵀg_+=0.
Proof: each actual stored entry has the assumed zero physical pairing. -/
theorem window_coordinates_zero (W : List (E × E)) (g : E)
    (ho : ∀ p∈W, inner ℝ p.1 g=0) : coordinates (windowSteps W) g=0 := by
  ext i
  exact ho (W.get i) (List.get_mem W i)

/-- Every actual member of the reference transcript is an executed earlier CG pair.
Use: derive augmented-model orthogonality without assuming a fictitious orthogonal stored history.
Article: main_krylov, lem:consistent(a), reference window.
Proof: a newest entry is the last true step; an older entry belongs to the shorter actual reference transcript. -/
theorem referencePairs_mem (Q : E →L[ℝ] E) (g : E) (k : ℕ) (p : E × E)
    (hp : p∈referencePairs Q g k) : ∃ j<k, p=(referenceStep Q g j,Q (referenceStep Q g j)) := by
  induction k with
  | zero => exact (List.not_mem_nil hp).elim
  | succ k ih =>
    rcases List.mem_cons.mp hp with he | he
    · exact ⟨k, Nat.lt_succ_self k, he⟩
    · obtain ⟨j,hj,he⟩ := ih he
      exact ⟨j, hj.trans (Nat.lt_succ_self k), he⟩

/-- The actual augmented quadratic window has zero projected post-search gradient.
Use: all RFC coefficient vectors, including repeated solves, vanish on the actual reference.
Article: main_krylov, lem:consistent(a), augmented U=[S,d].
Proof: the next actual CG invariant pairs its residual orthogonally with the
current direction and all earlier directions; true old steps are scalar multiples of these directions. -/
theorem reference_augmented_coordinates (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v)) (g : E) (k m : ℕ)
    (hg : CG.gradient Q g k≠0) :
    coordinates (windowSteps ((CG.direction Q g k,Q (CG.direction Q g k))::
      (referencePairs Q g k).take m)) (CG.gradient Q g (k+1))=0 := by
  -- The nonzero current residual certifies all gradients required by the computed next-state invariant.
  have hpre : ∀ i<k+1, CG.gradient Q g i≠0 := by
    intro i hi hz
    exact hg (CG.gradient_eq_zero_of_le Q g hz (by omega))
  have hk := CG.invariant Q hQ hpos g (k+1) hpre
  apply window_coordinates_zero
  intro p hp
  rcases List.mem_cons.mp hp with he | he
  · rw [he]
    exact hk.old_direction k (by omega)
  · obtain ⟨j,hj,he⟩ := referencePairs_mem Q g k p (List.mem_of_mem_take he)
    rw [he, referenceStep, real_inner_smul_left, hk.old_direction j (by omega), mul_zero]

end
end krylov.Methods
