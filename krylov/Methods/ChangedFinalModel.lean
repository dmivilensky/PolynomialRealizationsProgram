import krylov.Methods.HistoryModelArrays

/-!
Article: main_krylov, thm:C2(c) and apD:lem-model, genuine last-model policy.
Use: arbitrary observed-data terminal model changes preserve the true
at-most-one-query information class and global quadratic CG consistency.
Source: actual finite observed model arrays, true zero augmented reference
coordinates and the existing retained-policy quadratic execution induction.
-/

namespace krylov.Methods
noncomputable section
open Matrix Finset krylov.Reference
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
/-- A genuine one-query terminal correction using an arbitrary data-only additive change to the actual full observed model.
Use: the informed-base midpoint algorithm is an instance of this actual executor, including nonsmooth selectors and totalized impossible-data branches.
Article: main_krylov, thm:C2(c) and apD:lem-model, true changed final solve. -/
def changedFinalCorrection (N : ℕ)
    (D : History E → E → Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (H : History E) (z : E) : CorrectionTree E :=
  let d := (rfcMethod fullMemory 1).direction H
  let U := historyModelSteps N H d z
  let Z := historyModelImages N H d z
  repeatedModelTree U (pairModel U Z+D H z) 1 (searchedGradient H.gradient d z)

/-- The genuine RFC method with only its designated last model replaced by an arbitrary observed-data rule.
Use: actual one-correction source-class membership is proved for the eventual known-base midpoint instance.
Article: main_krylov, thm:C2(c), actual informed terminal policy. -/
def changedFinalMethod (N : ℕ)
    (D : History E → E → Matrix (Fin (N+1)) (Fin (N+1)) ℝ) : ProbedMethod E :=
  retainedMethod fullMemory (fun H z => if H.records.length=N then changedFinalCorrection N D H z
    else rfcCorrection fullMemory 1 H z)

/-- The true data-only changed-final-model policy has at most one actual correction on every continuation branch.
Use: the informed algorithm belongs to the original at-most-one-correction information regime.
Article: main_krylov, thm:C2(c), genuine query-count restriction.
Proof: the designated branch is one actual fixed-model query; every other
branch is the proved original one-correction RFC tree.
-/
theorem changedFinalMethod_oneCorrection (N : ℕ)
    (D : History E → E → Matrix (Fin (N+1)) (Fin (N+1)) ℝ) :
    OneCorrectionMethod (changedFinalMethod N D) := by
  intro H z
  change CorrectionsAtMostOne (if H.records.length=N then _ else _)
  split
  · intro _
    rfl
  · exact rfcMethod_oneCorrection fullMemory H z

/-- The actual changed terminal model never enlarges the genuine observed direction or augmented correction span, on any history.
Use: the source information restriction holds before any inverse, nondegeneracy or scenario assumption.
Article: main_krylov, thm:C2(c), original all-history source-class admissibility.
Proof: the actual direction is the original retained RFC direction. Each
fixed-array model vector belongs to the true augmented window span, including
zero defaults, so every genuine coefficient combination stays in that span.
-/
theorem changedFinalMethod_spanRestricted (N : ℕ)
    (D : History E → E → Matrix (Fin (N+1)) (Fin (N+1)) ℝ) :
    ProbedSpanRestricted fullMemory (changedFinalMethod N D) := by
  -- All physical correction vectors remain actual combinations of the original observed augmented window.
  intro H
  refine ⟨retained_direction_mem_observedSpan fullMemory H,?_⟩
  intro z
  change CorrectionTree.InSubspace _ (if H.records.length=N then _ else _)
  split
  · change _∈_ ∧ _
    refine ⟨?_,fun _ => trivial⟩
    apply Submodule.sum_mem
    intro i _
    apply Submodule.smul_mem
    rw [selectedWindow_full]
    exact getD_step_mem_windowSpan _ _
  · exact (rfcMethod_spanRestricted fullMemory 1 H).2 z

/-- Arbitrary actual observed-model replacement still makes zero physical correction on every genuine quadratic reference transcript.
Use: no regularity or vanishing-at-reference premise is imposed on the midpoint selector for global CG consistency.
Article: main_krylov, thm:C2(c), true quadratic consistency of the modified solve.
Proof: actual retained quadratic data give the genuine CG direction and
post-search residual. Its augmented observed coordinates vanish exactly,
including every stopped tail. Reading them into the true finite model array
preserves that zero right-hand side, so every actual changed-model coefficient
is zero regardless of the chosen data-only replacement matrix.
-/
theorem changedFinalCorrection_reference (N : ℕ)
    (D : History E → E → Matrix (Fin (N+1)) (Fin (N+1)) ℝ)
    (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v)) (g : E) (k : ℕ) (H : History E)
    (hg : H.gradient=CG.gradient Q g k) (hp : H.pairs=referencePairs Q g k) :
    let m := changedFinalMethod N D
    ZeroCorrections (changedFinalCorrection N D H (Q (m.direction H))) Q
      (searchedGradient H.gradient (m.direction H) (Q (m.direction H))) := by
  -- Actual quadratic augmented coordinates vanish before any modified inverse-model multiplication.
  have hd := retainedMethod_direction fullMemory
    (fun H z => if H.records.length=N then changedFinalCorrection N D H z else rfcCorrection fullMemory 1 H z)
    Q hQ hpos g k H hg hp (fun _ hk => hk)
  change (rfcMethod fullMemory 1).direction H=CG.direction Q g k at hd
  have hdm : (changedFinalMethod N D).direction H=CG.direction Q g k := hd
  unfold changedFinalCorrection
  dsimp only
  apply repeatedModelTree_zero
  rw [hd,hg,hdm]
  by_cases hz : CG.gradient Q g k=0
  · have hs : searchedGradient (CG.gradient Q g k) (CG.direction Q g k) (Q (CG.direction Q g k))=0 := by
      rw [hz,direction_zero_of_gradient Q g k hz]
      simp only [searchedGradient,map_zero,smul_zero,add_zero]
    rw [hs]
    ext i
    exact inner_zero_right _
  · have hc := reference_augmented_coordinates Q hQ hpos g k k hz
    have ht : (referencePairs Q g k).take k=referencePairs Q g k :=
      List.take_of_length_le (by rw [referencePairs_length])
    rw [ht] at hc
    change coordinates (fun i : Fin (N+1) =>
      (((CG.direction Q g k,Q (CG.direction Q g k))::H.pairs).getD i.val (0,0)).1) (CG.gradient Q g (k+1))=0
    rw [hp]
    exact getD_coordinates_zero _ _ hc N


/-- The actual data-only changed-final-model policy makes zero corrections on every genuine quadratic reference transcript, whether or not it is the designated final iteration.
Use: the same true quadratic induction covers the modified branch and the ordinary RFC continuation.
Article: main_krylov, thm:C2(c), global true reference correction rule.
Proof: the designated branch has the proved zero augmented right-hand
side for every data selector. Every other iteration uses the original
proved globally consistent RFC correction tree on the same real direction.
-/
theorem changedFinalMethod_reference (N : ℕ)
    (D : History E → E → Matrix (Fin (N+1)) (Fin (N+1)) ℝ)
    (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v)) (g : E) (k : ℕ) (H : History E)
    (hg : H.gradient=CG.gradient Q g k) (hp : H.pairs=referencePairs Q g k) :
    let m := changedFinalMethod N D
    ZeroCorrections (m.correction H (Q (m.direction H))) Q
      (searchedGradient H.gradient (m.direction H) (Q (m.direction H))) := by
  -- Both genuine branches retain the same actual retained quadratic direction.
  change ZeroCorrections (if H.records.length=N then _ else _) Q _
  split
  · exact changedFinalCorrection_reference N D Q hQ hpos g k H hg hp
  · exact rfcCorrection_reference fullMemory 1 Q hQ hpos g k H hg hp (fun _ hk => hk)

/-- The actual last-model replacement policy has precisely the genuine CG gradients and stored pairs on every positive quadratic, for every observed-data model selector.
Use: selector nonsmoothness and prior knowledge do not weaken the true global reference execution guarantee.
Article: main_krylov, thm:C2(c), actual changed-model quadratic run.
Proof: the existing retained-method induction uses the proved actual zero
correction rule on both the changed terminal branch and ordinary RFC continuation.
-/
theorem changedFinalMethod_static (N : ℕ)
    (D : History E → E → Matrix (Fin (N+1)) (Fin (N+1)) ℝ)
    (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v)) (g : E) (k : ℕ) :
    let H := methodRun (changedFinalMethod N D) (fun _ => Q) (fun _ => Q) g k
    H.gradient=CG.gradient Q g k ∧ H.pairs=referencePairs Q g k :=
  retainedMethod_static fullMemory _ Q hQ hpos g (fun _ _ hk => hk)
    (fun j H hg hp => changedFinalMethod_reference N D Q hQ hpos g j H hg hp) k

/-- The genuine one-query last-model replacement policy is globally CG-consistent for every actual observed-data replacement selector.
Use: the informed midpoint algorithm belongs to the original source minimax class without assuming a hypothetical consistency expansion.
Article: main_krylov, thm:C2(c), full actual CG-consistent class membership.
Proof: actual retained quadratic execution gives the true CG gradients
and pairs. The original real retained direction equals the genuine CG
direction with positive scale one, and both actual correction branches vanish.
-/
theorem changedFinalMethod_consistent (N : ℕ)
    (D : History E → E → Matrix (Fin (N+1)) (Fin (N+1)) ℝ) :
    CGConsistent (changedFinalMethod N D) := by
  -- Actual global consistency follows from the real quadratic run, including every stopped tail.
  intro Q hQ hpos g k
  have hs := changedFinalMethod_static N D Q hQ hpos g k
  refine ⟨1,zero_lt_one,?_,?_⟩
  · rw [one_smul]
    exact retainedMethod_direction fullMemory _ Q hQ hpos g k _ hs.1 hs.2 (fun _ hk => hk)
  · exact changedFinalMethod_reference N D Q hQ hpos g k _ hs.1 hs.2

end
end krylov.Methods
