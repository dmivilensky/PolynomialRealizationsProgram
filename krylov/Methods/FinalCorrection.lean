import krylov.Methods.RepeatedCorrection

/-!
Article: main_krylov, def:classes(M), alg:fc and prop:deep, final output query elision.
Use: execute every correction needed by a later solve while returning the
last correction as an actual unevaluated output with its exact saved query.
Source: the source's distinction between observed correction points and final outputs.
-/

namespace krylov.Methods
noncomputable section
open Matrix
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A finite adaptive correction protocol whose terminal displacement is a data-only unevaluated output.
Use: an output does not evaluate the unknown operator or supply an unobserved gradient to any later decision.
Article: main_krylov, def:classes(M), final point is not evaluated. -/
inductive FinalCorrectionTree (E : Type*) where
  /-- Return this terminal displacement without an oracle query. -/
  | output (step : E) : FinalCorrectionTree E
  /-- Observe the new gradient before choosing a further correction protocol. -/
  | query (step : E) (next : E → FinalCorrectionTree E) : FinalCorrectionTree E

/-- The actually evaluated correction movement, last observed gradient and unevaluated terminal displacement.
Use: the semantic final gradient is kept separate from the data returned by the actual oracle.
Article: main_krylov, def:classes(M), final correction accounting. -/
structure FinalCorrectionResult (E : Type*) where
  /-- Sum of actual evaluated correction displacements. -/
  movement : E
  /-- The last genuinely observed correction gradient. -/
  gradient : E
  /-- The final data-only displacement at which no gradient is observed. -/
  output : E
  /-- The complete actually queried correction trace. -/
  trace : List (E × E)

/-- Execute the final-output correction protocol, evaluating only genuine query nodes.
Use: the unknown output operator is applied only in the separate semantic analysis.
Article: main_krylov, alg:fc, observe unless returning the final point. -/
def runFinalCorrections (p : FinalCorrectionTree E) (B : E →L[ℝ] E) (g : E) : FinalCorrectionResult E :=
  match p with
  | .output u => ⟨0,g,u,[]⟩
  | .query u next =>
    let gnew := g+B u
    let r := runFinalCorrections (next gnew) B gnew
    ⟨u+r.movement,r.gradient,r.output,(u,gnew)::r.trace⟩

/-- Execute a prescribed number of fixed-model corrections with the final correction left unevaluated.
Use: every subsequent right-hand side uses an actual observed gradient; the last solve requires no further observation.
Article: main_krylov, alg:fc and prop:deep, last correction query is omitted. -/
def repeatedModelFinal (s : ι → E) (H : Matrix ι ι ℝ) : ℕ → E → FinalCorrectionTree E
  | 0, _ => .output 0
  | 1, g => .output (combine s (modelCoefficients s H g))
  | c+2, g => .query (combine s (modelCoefficients s H g)) (repeatedModelFinal s H (c+1))

/-- A positive fixed-model correction phase with c+1 corrections makes exactly c real gradient queries when its last point is returned.
Use: proves the saved final query from the actual query transcript, including the single-correction case.
Article: main_krylov, def:classes(M), every correction except the final output is evaluated.
Proof: each nonterminal correction contributes one actual query; the last correction contributes only its output. -/
theorem repeatedModelFinal_count (s : ι → E) (H : Matrix ι ι ℝ) (B : E →L[ℝ] E) (c : ℕ) (g : E) :
    (runFinalCorrections (repeatedModelFinal s H (c+1) g) B g).trace.length=c := by
  induction c generalizing g with
  | zero => rfl
  | succ c ih => exact congrArg Nat.succ (ih _)

/-- Every actual fixed-model correction query contributes exactly one observed gradient.
Use: compare the real fully evaluated phase with its output-aware execution.
Article: main_krylov, def:classes(M), correction query accounting.
Proof: the actual repeated query recursion adds one trace entry per correction. -/
theorem repeatedModelTree_count (s : ι → E) (H : Matrix ι ι ℝ) (B : E →L[ℝ] E) (c : ℕ) (g initial : E) :
    (runCorrections (repeatedModelTree s H c g) B initial).trace.length=c := by
  induction c generalizing g initial with
  | zero => rfl
  | succ c ih => exact congrArg Nat.succ (ih _ _)

/-- Eliding the final fixed-model correction query preserves its exact physical output and semantic final gradient.
Use: all RFC_k final outputs have the same mathematics while spending exactly one fewer gradient query.
Article: main_krylov, alg:fc and prop:deep, unevaluated final correction.
Proof: actual intermediate observed gradients and model solves agree by finite
induction; the last model correction is identical and its omitted gradient is reconstructed only for semantic comparison. -/
theorem repeatedModelFinal_exact (s : ι → E) (H : Matrix ι ι ℝ) (B : E →L[ℝ] E) (c : ℕ) (g : E) :
    let r := runFinalCorrections (repeatedModelFinal s H (c+1) g) B g
    let q := runCorrections (repeatedModelTree s H (c+1) g) B g
    r.movement+r.output=q.movement ∧ r.gradient+B r.output=q.gradient ∧
      r.trace=q.trace.take c := by
  -- Only the terminal query is omitted; no unobserved gradient reaches a continuation.
  induction c generalizing g with
  | zero => simp only [repeatedModelFinal,runFinalCorrections,repeatedModelTree,runCorrections,
      zero_add,add_zero,List.take_zero,and_self]
  | succ c ih =>
    obtain ⟨hm,hg,ht⟩ := ih (g+B (combine s (modelCoefficients s H g)))
    dsimp only [repeatedModelFinal,runFinalCorrections,repeatedModelTree,runCorrections]
    constructor
    · rw [add_assoc,hm]
      rfl
    constructor
    · exact hg
    · exact congrArg (List.cons _) ht

end
end krylov.Methods
