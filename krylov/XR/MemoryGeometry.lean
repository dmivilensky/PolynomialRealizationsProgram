import krylov.XR.MemoryRank
import krylov.XR.ModelStep

/-!
Article: main_krylov, thm:XR and thm:grow, chronological observation geometry.
Use: actual appending and anchor transport preserve the proved basis
invariants. These are list/finite-family identities, with no executor
success or trajectory assumption. Source: elementary span extension.
-/

namespace krylov.XR
noncomputable section
open Set krylov.Methods
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
/-- Actual stored steps generate precisely the physical steps in the list. -/
theorem storedSteps_range (W : List (PairObservation E)) :
    range (storedSteps W) = PairObservation.step '' {P | P ∈ W} := by
  ext s
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨W.get i, List.get_mem _ _, rfl⟩
  · rintro ⟨P, hP, rfl⟩
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hP
    exact ⟨i, congrArg PairObservation.step hi⟩

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
/-- Appending one real observation appends its actual physical generator. -/
theorem storedSteps_append_range (W : List (PairObservation E)) (P : PairObservation E) :
    range (storedSteps (W ++ [P])) = insert P.step (range (storedSteps W)) := by
  simp only [storedSteps_range, List.mem_append, List.mem_singleton]
  ext s
  constructor
  · rintro ⟨Q, hQ | rfl, rfl⟩
    · exact Or.inr ⟨Q, hQ, rfl⟩
    · exact Or.inl rfl
  · rintro (rfl | ⟨Q, hQ, rfl⟩)
    · exact ⟨P, Or.inr rfl, rfl⟩
    · exact ⟨Q, Or.inl hQ, rfl⟩

/-- A genuinely new stored step extends the independent chronological
family, including at a rejected probe which does not move the anchor. -/
theorem storedSteps_append_independent (W : List (PairObservation E))
    (P : PairObservation E) (hW : LinearIndependent ℝ (storedSteps W))
    (hP : P.step ∉ Submodule.span ℝ (range (storedSteps W))) :
    LinearIndependent ℝ (storedSteps (W ++ [P])) := by
  let idx : Fin (W ++ [P]).length → Fin (W.length + 1) := Fin.cast (by simp)
  have hi : Function.Injective idx := (Fin.cast_injective _)
  have he : storedSteps (W ++ [P]) = (Fin.snoc (storedSteps W) P.step) ∘ idx := by
    ext i
    by_cases h : i.val < W.length
    · dsimp only [Function.comp_apply, idx]
      simp [Fin.snoc, storedSteps, List.get_eq_getElem, h]
    · have heq : i.val = W.length := by have := i.isLt; simp only [List.length_append, List.length_singleton] at this; omega
      dsimp only [Function.comp_apply, idx]
      simp [Fin.snoc, storedSteps, List.get_eq_getElem, heq]
  rw [he]
  exact (hW.finSnoc hP).comp idx hi

/-- Anchor-pairing transport changes no actual step or its generated span. -/
theorem storedSteps_transport (W : List (PairObservation E)) (u : E) :
    range (storedSteps (W.map (fun P => P.transport u))) = range (storedSteps W) := by
  simp only [storedSteps_range]
  ext s
  simp only [mem_image, mem_ofPred_eq, List.mem_map]
  constructor
  · rintro ⟨P, ⟨Q, hQ, rfl⟩, hs⟩
    exact ⟨Q, hQ, hs⟩
  · rintro ⟨P, hP, hs⟩
    exact ⟨P.transport u, ⟨P, hP, rfl⟩, hs⟩

/-- Anchor transport preserves independence of the actual finite family. -/
theorem storedSteps_transport_independent (W : List (PairObservation E)) (u : E)
    (hW : LinearIndependent ℝ (storedSteps W)) :
    LinearIndependent ℝ (storedSteps (W.map (fun P => P.transport u))) := by
  let idx : Fin (W.map (fun P => P.transport u)).length → Fin W.length := Fin.cast (by simp)
  have he : storedSteps (W.map (fun P => P.transport u)) = storedSteps W ∘ idx := by
    ext i
    dsimp only [Function.comp_apply, idx]
    change ((W.map (fun P : PairObservation E => P.transport u))[i.val]).step = _
    rw [List.getElem_map]
    rfl
  rw [he]
  exact hW.comp idx (Fin.cast_injective _)

end
end krylov.XR
