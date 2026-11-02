import krylov.Methods.ObservedQueries
import krylov.Methods.ProbedModelBasis
import krylov.Methods.CorrectionCount
import krylov.Methods.InformationSpan

/-!
Article: main_krylov, thm:C2(c) and apD:lem-model, actual observed last-model replacement policy.
Use: execute a genuine data-only replacement of the final RFC model,
retain the full real RFC prefix and prove the exact source-class information
and global CG-consistency restrictions without assuming selector smoothness.
Source: true stored pair arrays, real model coefficients, original retained
CG direction and exact quadratic augmented-coordinate annihilation.
-/

namespace krylov.Methods
noncomputable section
open Matrix Finset krylov.Reference
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The true fixed finite array of augmented stored steps read only from the actual current direction and complete observed pair history.
Use: the modified terminal model has the original fixed coefficient dimension and real physical correction span.
Article: main_krylov, thm:C2(c), actual finite augmented model steps. -/
def historyModelSteps (N : ℕ) (H : History E) (d z : E) (i : Fin (N+1)) : E :=
  (((d,z)::H.pairs).getD i.val (0,0)).1

/-- The actual fixed finite array of augmented model images from the current probe and original observed stored secants.
Use: the modified terminal solve uses genuine measurements, including correction-contaminated prior secants.
Article: main_krylov, thm:C2(c), actual finite augmented model images. -/
def historyModelImages (N : ℕ) (H : History E) (d z : E) (i : Fin (N+1)) : E :=
  (((d,z)::H.pairs).getD i.val (0,0)).2

/-- Every actual zero-default finite pair-array step lies in the true observed window span.
Use: impossible out-of-range history data contribute only zero, so a fixed-size data-only model cannot enlarge the allowed physical correction span.
Article: main_krylov, thm:C2(c), actual all-history modified-model span restriction.
Proof: an available index is an actual original window column; an unavailable
index is the genuine zero default. Both belong to the true observed span.
-/
theorem getD_step_mem_windowSpan (W : List (E × E)) (i : ℕ) :
    (W.getD i (0,0)).1∈Submodule.span ℝ (Set.range (windowSteps W)) := by
  by_cases hi : i<W.length
  · let j : Fin W.length := ⟨i,hi⟩
    rw [List.getD_eq_get W (0,0) j]
    exact Submodule.subset_span ⟨j,rfl⟩
  · rw [List.getD_eq_default W (0,0) (by omega)]
    exact Submodule.zero_mem _

/-- A genuine zero projected window gradient remains zero in every fixed finite array read from that actual window, including zero-default entries.
Use: arbitrary data-only model changes retain exact global quadratic CG consistency.
Article: main_krylov, thm:C2(c), zero modified-model right-hand side on real quadratic data.
Proof: available entries read the original zero coordinate; unavailable
entries are the actual zero vector and have a zero true gradient pairing.
-/
theorem getD_coordinates_zero (W : List (E × E)) (g : E) (h : coordinates (windowSteps W) g=0)
    (N : ℕ) : coordinates (fun i : Fin (N+1) => (W.getD i.val (0,0)).1) g=0 := by
  -- Preserve actual zero window coordinates and the genuine zero default separately.
  ext i
  change inner ℝ (W.getD i.val (0,0)).1 g=0
  by_cases hi : i.val<W.length
  · let j : Fin W.length := ⟨i.val,hi⟩
    rw [List.getD_eq_get W (0,0) j]
    exact congrFun h j
  · rw [List.getD_eq_default W (0,0) (n := i.val) (by omega)]
    exact inner_zero_left _

omit [InnerProductSpace ℝ E] in
/-- Reading a true available finite executed-pair array index with a zero default gives its exact original chronological pair.
Use: the actual fixed model arrays share precisely the original executor's observed step/secant indices.
Article: main_krylov, thm:C2(c), true finite zero-default stored-pair reconstruction.
Proof: the actual index is available by its true transcript length, so reuse genuine chronological pair indexing. -/
theorem executedPairs_getD (s y : ℕ → E) (k i : ℕ) (hi : i<k) :
    (executedPairs s y k).getD i (0,0)=(s (k-1-i),y (k-1-i)) := by
  rw [List.getD_eq_getElem _ (0,0) (by rw [executedPairs_length]; exact hi)]
  exact executedPairs_get s y k i hi

/-- The actual fixed finite augmented model-step array read from genuine history is exactly the existing real full probed step basis.
Use: identify the true data-only changed-policy solve with the actual native model used by the proved cubic expansion.
Article: main_krylov, thm:C2(c) and apD:lem-model, exact genuine step-basis coordinates.
Proof: the head is the actual current raw direction. Every old coordinate
reads its true executed step from the same original newest-first pair history.
-/
theorem historyModelSteps_run (m : ProbedMethod E) (A B : ℕ → E →L[ℝ] E) (g : E) (N : ℕ) :
    historyModelSteps N (methodRun m A B g N) (probedDirection m A B g N) (probedProbe m A B g N)=
      probedStepBasis m A B g N := by
  -- Recover each actual old model column from its genuine observed chronological step.
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · change ((methodRun m A B g N).pairs.getD j.val (0,0)).1=probedStep m A B g (N-1-j.val)
    rw [methodRun_pairs_executed,executedPairs_getD _ _ N j.val j.isLt]

/-- The true fixed finite augmented model-image array is exactly the actual current probe and genuine earlier observed secants.
Use: the real informed model never replaces correction-contaminated history by hypothetical exact line images.
Article: main_krylov, thm:C2(c) and apD:lem-model, exact genuine observed-image coordinates.
Proof: the head is the actual current measurement. Every old coordinate
reads its original executed secant from the genuine complete pair history.
-/
theorem historyModelImages_run (m : ProbedMethod E) (A B : ℕ → E →L[ℝ] E) (g : E) (N : ℕ) :
    historyModelImages N (methodRun m A B g N) (probedDirection m A B g N) (probedProbe m A B g N)=
      probedImageBasis m A B g N := by
  -- Recover each original measured old image from its actual executed chronological secant.
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · change ((methodRun m A B g N).pairs.getD j.val (0,0)).2=probedSecant m A B g (N-1-j.val)
    rw [methodRun_pairs_executed,executedPairs_getD _ _ N j.val j.isLt]

end
end krylov.Methods
