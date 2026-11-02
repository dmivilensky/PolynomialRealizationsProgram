import krylov.Methods.RFCCoordinates

/-!
Article: main_krylov, alg:fc and lem:U(d), unconditional true RFC array formula.
Use: express the actual observed gate and actual correction tree in fixed
chronological-age coordinates on every history, including skipped gates.
Source: the proved real retained-window indexing, defect norm invariance
and full actual model-query tree reindexing.
-/

namespace krylov.Methods
noncomputable section
open krylov.Reference
open scoped Matrix.Norms.L2Operator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The genuine gated RFC correction tree equals its finite chronological-age coordinate formula in both gate branches.
Use: actual scaling and regularity proofs retain the real observed gate instead of assuming a fixed branch.
Article: main_krylov, alg:fc and lem:U(d).
Proof: the actual window length determines emptiness, actual coordinate
reindexing preserves the spectral defect norm, and the accepted branch has
the proved full physical model-query tree coordinate formula. -/
theorem rfcCorrection_array (memory : ℕ → ℕ) (count : ℕ) (H : History E)
    (s y : ℕ → E) (k : ℕ) (d z : E) (hshape : H.pairs=executedPairs s y k)
    (hd : d=windowDirection (selectedWindow memory H) H.gradient) :
    let S := fun i : Fin (min (memory k) k) => s (k-1-i.val)
    let Y := fun i : Fin (min (memory k) k) => y (k-1-i.val)
    let U : Fin (min (memory k) k+1) → E := Fin.cons d S
    let Z : Fin (min (memory k) k+1) → E := Fin.cons z Y
    rfcCorrection memory count H z=
      if 0<min (memory k) k ∧ ‖pairDefect S Y‖<1 then
        repeatedModelTree U (pairModel U Z) count (searchedGradient H.gradient d z) else .done := by
  -- The branch equivalence uses the real retained transcript before rewriting either actual tree.
  let W := selectedWindow memory H
  have hw : W=(executedPairs s y k).take (memory k) :=
    selectedWindow_of_executed_pairs memory H s y k hshape
  have hl : W.length=min (memory k) k := by rw [hw,List.length_take,executedPairs_length]
  have he : W≠[] ↔ 0<min (memory k) k := by
    rw [← hl,List.length_pos_iff_ne_nil]
  have hn : ‖windowDefect W‖=‖pairDefect
      (fun i : Fin (min (memory k) k) => s (k-1-i.val))
      (fun i : Fin (min (memory k) k) => y (k-1-i.val))‖ := by
    rw [hw]
    have ht := retainedWindow_coordinates s y k (memory k)
    exact windowDefect_norm_of_coordinates _ _ _ _ ht.1 ht.2
  dsimp only
  by_cases hg : W≠[] ∧ ‖windowDefect W‖<1
  · rw [ite_eq_left (show 0<min (memory k) k ∧ _ from ⟨he.mp hg.1,hn ▸ hg.2⟩)]
    exact rfcCorrection_coordinates memory count H s y k d z hshape hd hg
  · rw [ite_eq_right (show ¬(0<min (memory k) k ∧ _) from fun h => hg ⟨he.mpr h.1,hn.symm ▸ h.2⟩)]
    change ¬(selectedWindow memory H≠[] ∧ ‖windowDefect (selectedWindow memory H)‖<1) at hg
    simp only [rfcCorrection,ite_eq_right hg]

end
end krylov.Methods
