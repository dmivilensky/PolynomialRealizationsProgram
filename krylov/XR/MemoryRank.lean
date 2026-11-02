import krylov.XR.AlgorithmModel

/-!
Article: main_krylov, alg:xr, actual retained-window rank invariants.
Use: derive rank and memory bounds from the finite cleanup searches, and
show that genuinely independent unrefuted data are retained unchanged.
Source: ordered suffix restriction of linearly independent finite families.
-/

namespace krylov.XR
noncomputable section
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
/-- Dropping an old prefix selects its real chronological step indices. -/
theorem storedSteps_drop (W : List (PairObservation E)) (o : ℕ)
    (i : Fin (W.drop o).length) :
    storedSteps (W.drop o) i = storedSteps W
      ⟨o + i.val, by have hi := i.isLt; have hl : (W.drop o).length = W.length - o := List.length_drop; omega⟩ := by
  simp only [storedSteps, List.get_eq_getElem, List.getElem_drop]

/-- Every retained suffix of an actual independent step family is
independent, including empty suffixes. -/
theorem storedSteps_drop_independent (W : List (PairObservation E))
    (hW : LinearIndependent ℝ (storedSteps W)) (o : ℕ) :
    LinearIndependent ℝ (storedSteps (W.drop o)) := by
  let idx : Fin (W.drop o).length → Fin W.length := fun i =>
    ⟨o + i.val, by have hi := i.isLt; have hl : (W.drop o).length = W.length - o := List.length_drop; omega⟩
  have hi : Function.Injective idx := by
    intro i j hij
    apply Fin.ext
    have he := congrArg Fin.val hij
    dsimp only [idx] at he
    omega
  have he : storedSteps (W.drop o) = storedSteps W ∘ idx :=
    funext fun i => storedSteps_drop W o i
  rw [he]
  exact hW.comp idx hi

/-- The rank loop really returns an independent actual suffix. -/
theorem rankWindow_independent (dimension : ℕ) (S : State E) :
    LinearIndependent ℝ (storedSteps (rankWindow dimension S)) := by
  classical
  exact (Nat.find_spec (exists_independent_suffix
    (retainNewest (min S.capacity dimension) S.pairs))).2

/-- The full concrete ModelStep always returns independent columns. -/
theorem algorithmModel_independent {n : ℕ} (P : Parameters)
    (S : State (EuclideanSpace ℝ (Fin n))) :
    LinearIndependent ℝ (storedSteps (algorithmModel P S).pairs) :=
  storedSteps_drop_independent _ (rankWindow_independent n S) _

/-- Rank cleanup deletes nothing from genuinely independent data. -/
theorem rankDeletion_eq_zero (W : List (PairObservation E))
    (hW : LinearIndependent ℝ (storedSteps W)) : rankDeletion W = 0 := by
  classical
  apply Nat.eq_zero_of_le_zero
  exact Nat.find_min' (exists_independent_suffix W)
    ⟨Nat.zero_le _, (List.drop_zero (l := W)).symm ▸ hW⟩

/-- The literal window test deletes nothing from an unrefuted window. -/
theorem modelDeletion_eq_zero (P : Parameters) (W : List (PairObservation E))
    (hW : windowUnrefuted P.windowThreshold (storedPairing W)) : modelDeletion P W = 0 := by
  have he : windowSuffix (storedPairing W) 0 = storedPairing W := by
    ext i j
    simp [windowSuffix, windowSuffixIndex]
  have hz : unrefutedSuffix P.windowThreshold (storedPairing W) = 0 := by
    apply Nat.eq_zero_of_le_zero
    exact unrefutedSuffix_minimal _ _ 0 (Nat.zero_le _) (he.symm ▸ hW)
  simp only [modelDeletion, hz, Nat.min_eq_left (Nat.zero_le _)]

/-- Concrete ModelStep respects the requested capacity and ambient rank. -/
theorem algorithmModel_length_le {n : ℕ} (P : Parameters)
    (S : State (EuclideanSpace ℝ (Fin n))) :
    (algorithmModel P S).pairs.length ≤ min S.capacity n := by
  change ((rankWindow n S).drop _).length ≤ _
  simp only [rankWindow, List.length_drop, retainNewest_length]
  omega

end
end krylov.XR
