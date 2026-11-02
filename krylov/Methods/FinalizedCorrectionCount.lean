import krylov.Methods.FinalizedMethod
import krylov.Methods.CorrectionFreeClasses

set_option autoImplicit false
/-!
Article: main_krylov, s3:cor:qn, actual single-correction final wrappers.
Use: prove the genuine final latest-information wrapper of every correction-free
method belongs to the true at-most-one-correction source subclass.
Source: actual complete correction-tree branches and genuine raw correction-free decisions.
-/

namespace krylov.Methods
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The genuine final wrapper of every actual correction-free raw method uses at most one real correction on every possible observed branch.
Use: The genuine final wrapper of every actual correction-free raw method uses at most one real correction on every possible observed branch.
Article: main_krylov, s3:cor:qn, actual single-correction final wrappers.
Proof: The original phase is genuinely empty, the real appended model tree has one query with immediate termination, and every later FC phase is empty. -/
theorem finalizedMethod_oneCorrection (m : ProbedMethod E) (hm : CorrectionFree m) (N : ℕ) :
    OneCorrectionMethod (finalizedMethod m N) := by
  -- Inspect all genuine horizon branches, including arbitrary observations away from the reference.
  intro H z
  change CorrectionsAtMostOne (if H.records.length+1=N then _ else _)
  split
  · rw [hm]
    intro _
    rfl
  · split
    · rw [hm]
      trivial
    · trivial
end
end krylov.Methods
