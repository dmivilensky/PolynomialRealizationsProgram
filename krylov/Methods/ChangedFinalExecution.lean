import krylov.Methods.ChangedFinalModel

/-!
Article: main_krylov, thm:C2(c), true execution with an observed model change.
Use: the genuine changed-model policy preserves its complete actual RFC
prefix and returns exactly its real one-query modified terminal gradient.
Source: actual record-count branch selection and the true nonanticipating
probe/line-search/correction executor, with every original observation retained.
-/

namespace krylov.Methods
noncomputable section
open Matrix Finset krylov.Reference
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
/-- Every original operator scenario has exactly the genuine full RFC history before the designated changed terminal correction.
Use: all native cubic model and incoming-vector estimates apply to the actual informed algorithm's unchanged executed prefix.
Article: main_krylov, thm:C2(c), preservation of the complete actual RFC prefix.
Proof: induct through real histories. Every actual earlier record count
selects the unchanged RFC correction branch, and the direction is the same
real retained direction throughout the genuine prefix.
-/
theorem changedFinalMethod_run_before (N : ℕ)
    (D : History E → E → Matrix (Fin (N+1)) (Fin (N+1)) ℝ)
    (A B : ℕ → E →L[ℝ] E) (g : E) (k : ℕ) (hk : k≤N) :
    methodRun (changedFinalMethod N D) A B g k=methodRun (rfcMethod fullMemory 1) A B g k := by
  -- Every actual earlier iteration selects exactly the genuine original direction and correction tree.
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [methodRun,methodRun,ih (by omega)]
    unfold methodAdvance
    simp only [changedFinalMethod,retainedMethod,methodRun_length,rfcMethod,
      ite_eq_right (by omega : ¬ k=N)]

/-- The actual returned gradient of the changed-final-model method is precisely its genuine post-search gradient plus its one real changed-model correction action.
Use: identify the actual policy executor with the concrete terminal model solve used in the source expansion.
Article: main_krylov, thm:C2(c) and apD:lem-model, actual changed-policy terminal output.
Proof: the complete actual prefix equals ordinary RFC. The true final
record count selects exactly one real coefficient-model query, whose genuine
operator answer is the actual returned terminal gradient.
-/
theorem changedFinalMethod_gradient_last (N : ℕ)
    (D : History E → E → Matrix (Fin (N+1)) (Fin (N+1)) ℝ)
    (A B : ℕ → E →L[ℝ] E) (g : E) :
    let H := methodRun (rfcMethod fullMemory 1) A B g N
    let d := (rfcMethod fullMemory 1).direction H
    let z := A N d
    let U := historyModelSteps N H d z
    let Z := historyModelImages N H d z
    probedGradient (changedFinalMethod N D) A B g (N+1)=
      searchedGradient H.gradient d z+B N (combine U
        (modelCoefficients U (pairModel U Z+D H z) (searchedGradient H.gradient d z))) := by
  -- The only changed real query occurs after the original genuine complete RFC prefix.
  unfold probedGradient
  rw [methodRun,changedFinalMethod_run_before N D A B g N le_rfl]
  change (runCorrections _ _ _).gradient=_
  simp only [changedFinalMethod,retainedMethod,methodRun_length,changedFinalCorrection,
    repeatedModelTree]
  rfl


end
end krylov.Methods
