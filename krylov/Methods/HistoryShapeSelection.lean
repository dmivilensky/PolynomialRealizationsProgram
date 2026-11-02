import krylov.Methods.HistoryShape

set_option autoImplicit false
/-!
Article: main_krylov, def:classes and cor:lm, true finite history-shape selection.
Use: select primitive coefficient programs on the actual observed dimension
of a genuine reference run, preserving all real correction-query boundaries.
Source: genuine complete-history observation counts and elementary strict
monotonicity of the true number of observed vectors.
-/

namespace krylov.Methods
noncomputable section
open krylov.Reference
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The genuine number of available observed vectors increases strictly along every actual probed execution.
Use: The genuine number of available observed vectors increases strictly along every actual probed execution.
Article: main_krylov, def:classes and cor:lm, true finite history-shape selection.
Proof: Count the true four main iteration observations and the two actual observations of each genuine correction query. -/
theorem methodRun_observationLength_strictMono (m : ProbedMethod E) (A B : ℕ → E →L[ℝ] E) (g : E) :
    StrictMono (fun k => (methodRun m A B g k).observationList.length) := by
  apply strictMono_nat_of_lt_succ
  intro k
  -- Every genuine iteration contributes its real main observations even when no correction is queried.
  let H := methodRun m A B g k
  let T := runCorrections (m.correction H (A k (m.direction H))) (B k)
    (searchedGradient H.gradient (m.direction H) (A k (m.direction H)))
  have hs : (methodRun m A B g (k+1)).queryShape=T.trace.length::H.queryShape := rfl
  rw [History.observationList_length_shape,History.observationList_length_shape,hs,List.map_cons,List.sum_cons]
  change 2+(H.queryShape.map (fun k => 4+2*k)).sum<2+(4+2*T.trace.length+(H.queryShape.map (fun k => 4+2*k)).sum)
  omega

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
/-- The actual reference query shape selected solely by a true observed-vector count.
Use: The actual reference query shape selected solely by a true observed-vector count.
Article: main_krylov, def:classes and cor:lm, true finite history-shape selection.
Proof: Use the genuine reference record shape at the unique matching actual observed dimension, with empty shape as the total default. -/
def selectedHistoryShape (H : ℕ → History E) (n : ℕ) : List ℕ := by
  classical
  exact if h : ∃ k, (H k).observationList.length=n then (H (Nat.find h)).queryShape else []

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
/-- The dimension-selected genuine query shape is exactly the actual reference history shape at every true iteration.
Use: The dimension-selected genuine query shape is exactly the actual reference history shape at every true iteration.
Article: main_krylov, def:classes and cor:lm, true finite history-shape selection.
Proof: Strict increase gives uniqueness of the true matching reference observation count. -/
theorem selectedHistoryShape_actual (H : ℕ → History E)
    (hH : StrictMono (fun k => (H k).observationList.length)) (k : ℕ) :
    selectedHistoryShape H (H k).observationList.length=(H k).queryShape := by
  have he : ∃ j, (H j).observationList.length=(H k).observationList.length := ⟨k,rfl⟩
  rw [selectedHistoryShape,dite_eq_left he,hH.injective (Nat.find_spec he)]
end
end krylov.Methods
