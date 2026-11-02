import krylov.Methods.ChangedFinalExecution
import krylov.Correction.TerminalModel
import krylov.Information.MinimaxValue

/-!
Article: main_krylov, thm:C2(c) and apD:lem-model, actual informed-policy execution.
Use: identify the genuine observed-model policy with the proved actual
modified terminal solve and place it in the original minimax method class.
Source: exact original history-array identities and global quadratic
consistency of arbitrary data-only last-model replacements.
-/

namespace krylov.Information
noncomputable section
open Matrix krylov.Reference krylov.Methods krylov.Correction
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual changed-policy output is precisely the genuine modified terminal model solve after its full original RFC prefix.
Use: apply the proved cubic expansion to the real informed algorithm.
Article: main_krylov, thm:C2(c) and apD:lem-model, exact true terminal execution.
Proof: identify each actual stored model array with the genuine probed basis and reuse the actual final-query execution identity. -/
theorem changedFinalMethod_modifiedGradient (N : ℕ)
    (D : History E → E → Matrix (Fin (N+1)) (Fin (N+1)) ℝ)
    (A B : ℕ → E →L[ℝ] E) (g : E) :
    probedGradient (changedFinalMethod N D) A B g (N+1)=
      modifiedTerminalGradient A B g N
        (D (methodRun (rfcMethod fullMemory 1) A B g N) (probedProbe (rfcMethod fullMemory 1) A B g N)) := by
  rw [changedFinalMethod_gradient_last]
  have hs := historyModelSteps_run (rfcMethod fullMemory 1) A B g N
  have hz := historyModelImages_run (rfcMethod fullMemory 1) A B g N
  dsimp only [probedDirection,probedProbe] at hs hz
  simp only [hs,hz]
  rfl

/-- Every data-only final-model replacement is a genuine globally CG-consistent one-correction source strategy.
Use: the informed construction enters the actual method infimum without any selector smoothness premise.
Article: main_krylov, thm:C2(c), genuine source-class membership. -/
def changedFinalStrategy (N : ℕ)
    (D : History E → E → Matrix (Fin (N+1)) (Fin (N+1)) ℝ) : OneCorrectionCGStrategy E :=
  ⟨⟨fullMemory,changedFinalMethod N D,changedFinalMethod_spanRestricted N D⟩,
    changedFinalMethod_consistent N D,changedFinalMethod_oneCorrection N D⟩

end
end krylov.Information
