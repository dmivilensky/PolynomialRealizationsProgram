import krylov.Methods.RFC

set_option autoImplicit false
/-!
Article: main_krylov, thm:select, actual at-most-one-correction source class.
Use: express the genuine selection subclass with at most one real
correction query per iteration on every true continuation branch, and
verify actual one-correction RFC belongs to it.
Source: genuine finite nonanticipating correction trees and the actual
gated repeated-model RFC executor.
-/

namespace krylov.Methods
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The genuine correction-tree property allowing at most one true query for every actual continuation answer.
Use: The genuine correction-tree property allowing at most one true query for every actual continuation answer.
Article: main_krylov, thm:select, actual at-most-one-correction source class.
Proof: A real empty phase is allowed; every genuine first-query continuation must stop immediately. -/
def CorrectionsAtMostOne : CorrectionTree E → Prop
  | .done => True
  | .query _ next => ∀ gnew : E, next gnew=.done

/-- The actual selection subclass property requiring at most one genuine correction per real iteration on every observed history.
Use: The actual selection subclass property requiring at most one genuine correction per real iteration on every observed history.
Article: main_krylov, thm:select, actual at-most-one-correction source class.
Proof: Impose the true correction-tree query bound on every actual history and probe decision. -/
def OneCorrectionMethod (m : ProbedMethod E) : Prop := ∀ H z, CorrectionsAtMostOne (m.correction H z)

/-- Actual gated one-correction RFC satisfies the genuine at-most-one-correction subclass property for every true memory rule.
Use: Actual gated one-correction RFC satisfies the genuine at-most-one-correction subclass property for every true memory rule.
Article: main_krylov, thm:select, actual at-most-one-correction source class.
Proof: Inspect the actual observed gate: the true rejected branch stops, and every genuine accepted first query has an actual immediately stopping continuation. -/
theorem rfcMethod_oneCorrection (memory : ℕ → ℕ) : OneCorrectionMethod (rfcMethod memory 1 : ProbedMethod E) := by
  -- Both genuine observed gate branches preserve the actual one-query correction bound.
  intro H z
  change CorrectionsAtMostOne (rfcCorrection memory 1 H z)
  unfold rfcCorrection
  dsimp only
  split
  · intro _
    rfl
  · trivial
end
end krylov.Methods
