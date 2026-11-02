import krylov.Functions.GlobalValueContinuation

/-!
Article: main_krylov, thm:Fplanar, genuine endpoint-only final reader.
Use: reconstruct the final scalar observation data from the actual cached
history, its real retained step/secant pairs and the current observed probe.
Past gradients are cached record fields; the searched gradient is computed
from its genuine line update. Only values at retained actual endpoints are
read from the scalar objective. No derivative or unknown operator is an input.
-/
namespace krylov.Functions
noncomputable section
open Finset krylov.Methods krylov.Reference
open scoped InnerProductSpace BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- An actual chronological retained step, with zero outside the real
stored history. Article: main_krylov, thm:Fplanar. -/
def endpointPastStep (H : History E) (i : ℕ) : E :=
  ((H.pairs.reverse[i]?).map Prod.fst).getD 0

/-- A genuine cached endpoint gradient, with the initial observed gradient
at zero and zero outside the real stored history. Article: thm:Fplanar. -/
def endpointPastGradient (H : History E) (i : ℕ) : E :=
  if i=0 then H.initial else ((H.records.reverse[i-1]?).map IterationRecord.gradient).getD 0

/-- The actual current raw searched step calculated from the observed
current gradient, chosen direction and current probe. Article: thm:Fplanar. -/
def endpointCurrentStep (m : ProbedMethod E) (H : History E) (z : E) : E :=
  lineLength H.gradient (m.direction H) z • m.direction H

/-- The actual retained prefix steps followed by the current searched
step, in chronological order. Article: main_krylov, thm:Fplanar. -/
def endpointReaderStep (m : ProbedMethod E) (N : ℕ) (H : History E) (z : E) (i : ℕ) : E :=
  if i+1=N then endpointCurrentStep m H z else endpointPastStep H i

/-- The actual retained endpoint locations and the newly searched endpoint.
All positions are reconstructed from observed displacement data.
Article: main_krylov, thm:Fplanar. -/
def endpointReaderPoint (m : ProbedMethod E) (N : ℕ) (x₀ : E) (H : History E) (z : E) (i : ℕ) : E :=
  if i=N then x₀+H.displacement+endpointCurrentStep m H z else
    x₀+∑ j∈range i,endpointPastStep H j

/-- The concrete scalar endpoint reader. Whole-line fields are dummy zero:
the admitted centre reads only values, cached gradients and true steps.
Thus this constructor promises no additional line-objective access.
Article: main_krylov, thm:Fplanar, original value-information protocol. -/
def endpointValueReader (m : ProbedMethod E) (N : ℕ) (f : E → ℝ) (x₀ : E)
    (H : History E) (z : E) : FunctionSearchTranscript E N where
  points i := endpointReaderPoint m N x₀ H z i.val
  lineSteps i := endpointReaderStep m N H z i.val
  values i := f (endpointReaderPoint m N x₀ H z i.val)
  gradients i := if i.val=N then searchedGradient H.gradient (m.direction H) z else endpointPastGradient H i.val
  lineObjectives _ _ := 0

/-- The concrete reader reports exactly the actual searched gradient, by
the observed line update itself. Article: main_krylov, thm:Fplanar. -/
theorem endpointValueReader_final_gradient (m : ProbedMethod E) (N : ℕ)
    (f : E → ℝ) (x₀ : E) (H : History E) (z : E) :
    observedFinalGradient (endpointValueReader m N f x₀ H z)=
      searchedGradient H.gradient (m.direction H) z := by
  simp only [observedFinalGradient,endpointValueReader,ite_true]

end
end krylov.Functions
