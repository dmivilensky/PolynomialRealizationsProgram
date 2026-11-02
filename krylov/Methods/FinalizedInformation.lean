import krylov.Methods.FinalizedMethod
import krylov.Methods.InformationSpan

set_option autoImplicit false
/-!
Article: main_krylov, thm:select and apB:lem:mu(a), genuine final-correction source information membership.
Use: prove the actual arbitrary-method final latest-information wrapper
respects the true source direction and all-branch correction-span
restrictions on every genuine observed history.
Source: actual finite stored-window inclusion and the genuine appended
correction-tree subspace theorem, with the true full observed model basis.
-/

namespace krylov.Methods
noncomputable section
open krylov.Reference
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Enlarging the genuine allowed subspace preserves actual all-branch correction-tree admissibility.
Use: Enlarging the genuine allowed subspace preserves actual all-branch correction-tree admissibility.
Article: main_krylov, thm:select and apB:lem:mu(a), genuine final-correction source information membership.
Proof: Induct through each real query and every true possible returned gradient. -/
theorem CorrectionTree.inSubspace_mono (p : CorrectionTree E) (K L : Submodule ℝ E)
    (hKL : K≤L) (hp : p.InSubspace K) : p.InSubspace L := by
  induction p with
  | done => trivial
  | query u next ih => exact ⟨hKL hp.1,fun v => ih v (hp.2 v)⟩

/-- Including actual stored pairs includes their genuine finite step spans.
Use: Including actual stored pairs includes their genuine finite step spans.
Article: main_krylov, thm:select and apB:lem:mu(a), genuine final-correction source information membership.
Proof: Map each true finite stored-pair coordinate into its actual containing list before taking real linear spans. -/
theorem windowSpan_mono (W V : List (E × E)) (h : ∀ p∈W, p∈V) :
    Submodule.span ℝ (Set.range (windowSteps W))≤Submodule.span ℝ (Set.range (windowSteps V)) := by
  apply Submodule.span_mono
  rintro _ ⟨i,rfl⟩
  obtain ⟨j,hj⟩ := List.mem_iff_get.mp (h _ (List.get_mem W i))
  exact ⟨j,congrArg Prod.fst hj⟩

/-- Appending the actual final full-history latest-information correction to any genuine source-admissible method gives a true full-memory source-admissible policy on every actual input history.
Use: Appending the actual final full-history latest-information correction to any genuine source-admissible method gives a true full-memory source-admissible policy on every actual input history.
Article: main_krylov, thm:select and apB:lem:mu(a), genuine final-correction source information membership.
Proof: The original actual retained augmented span lies in the genuine full augmented span. Both real original and appended correction phases stay in that actual full span; after the true horizon the genuine FC continuation is source-admissible. -/
theorem finalizedMethod_spanRestricted (memory : ℕ → ℕ) (m : ProbedMethod E)
    (hm : ProbedSpanRestricted memory m) (N : ℕ) :
    ProbedSpanRestricted fullMemory (finalizedMethod m N) := by
  -- The genuine original retained correction span is included in the actual full augmented span, preserving all true future-answer branches.
  intro H
  by_cases hk : H.records.length<N
  · have hd := finalizedMethod_direction_before m N H hk
    refine ⟨hd ▸ (hm H).1,?_⟩
    intro z
    rw [hd,selectedWindow_full]
    let K := Submodule.span ℝ (Set.range (windowSteps ((m.direction H,z)::H.pairs)))
    have hle : Submodule.span ℝ (Set.range (windowSteps ((m.direction H,z)::selectedWindow memory H)))≤K := by
      apply windowSpan_mono
      intro p hp
      rcases List.mem_cons.mp hp with he|he
      · exact List.mem_cons.mpr (Or.inl he)
      · exact List.mem_cons.mpr (Or.inr (List.mem_of_mem_take he))
    -- Every genuine appended model query is a true combination of the actual same full augmented observed basis.
    have hp : (m.correction H z).InSubspace K := CorrectionTree.inSubspace_mono _ _ _ hle ((hm H).2 z)
    change CorrectionTree.InSubspace K (if H.records.length+1=N then _ else if H.records.length<N then _ else _)
    by_cases he : H.records.length+1=N
    · rw [ite_eq_left he]
      apply CorrectionTree.follow_inSubspace _ _ _ _ hp
      intro v
      exact repeatedModelTree_inSubspace _ _ 1 v
    · rw [ite_eq_right he,ite_eq_left hk]
      exact hp
  · have hd := finalizedMethod_direction_after m N H (by omega)
    refine ⟨hd ▸ (fcMethod_spanRestricted fullMemory H).1,?_⟩
    intro z
    change CorrectionTree.InSubspace _ (if H.records.length+1=N then _ else if H.records.length<N then _ else _)
    rw [ite_eq_right (by omega),ite_eq_right hk]
    trivial
end
end krylov.Methods
