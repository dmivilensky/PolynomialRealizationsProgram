import krylov.Methods.DeferredDirection
import krylov.Methods.InformationSpan
import krylov.Methods.CorrectionFree

set_option autoImplicit false
/-!
Article: main_krylov, s3:def:DC and apB:lem:mu(d), genuine deferred-cancellation raw method.
Use: implement the actual finite-horizon deferred direction change with
true observed data, real empty corrections and genuine span restrictions.
Source: actual source deferred conjugacy formula and the proved real
current-gradient/stored-step observation spans.
-/

namespace krylov.Methods
noncomputable section
open krylov.Reference
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The genuine deferred-cancellation policy changes the true FC direction at its actual prescribed last iteration and makes no correction query.
Use: The genuine deferred-cancellation policy changes the true FC direction at its actual prescribed last iteration and makes no correction query.
Article: main_krylov, s3:def:DC and apB:lem:mu(d), genuine deferred-cancellation raw method.
Proof: Use the real observed record count to select the genuine tilted solve and continue by actual FC elsewhere. -/
def deferredMethod (memory : ℕ → ℕ) (N : ℕ) (a : ℝ) : ProbedMethod E where
  direction H := if H.records.length+1=N then
    deferredDirection (windowSteps (selectedWindow memory H)) (windowImages (selectedWindow memory H)) H.gradient a
    else (fcMethod memory).direction H
  correction _ _ := .done

/-- The actual deferred-cancellation policy belongs to the genuine correction-free source subclass on every observed history.
Use: The actual deferred-cancellation policy belongs to the genuine correction-free source subclass on every observed history.
Article: main_krylov, s3:def:DC and apB:lem:mu(d), genuine deferred-cancellation raw method.
Proof: Its real correction decision is always empty. -/
theorem deferredMethod_correctionFree (memory : ℕ → ℕ) (N : ℕ) (a : ℝ) :
    CorrectionFree (deferredMethod memory N a : ProbedMethod E) := fun _ _ => rfl

/-- True zero old-step gradient coordinates make the genuine deferred policy choose exactly the actual FC direction.
Use: True zero old-step gradient coordinates make the genuine deferred policy choose exactly the actual FC direction.
Article: main_krylov, s3:def:DC and apB:lem:mu(d), genuine deferred-cancellation raw method.
Proof: The real tilted branch agrees with genuine conjugacy on the true zero-residual right-hand side. -/
theorem deferredMethod_direction_eq_FC (memory : ℕ → ℕ) (N : ℕ) (a : ℝ) (H : History E)
    (hz : coordinates (windowSteps (selectedWindow memory H)) H.gradient=0) :
    (deferredMethod memory N a).direction H=(fcMethod memory).direction H := by
  change (if H.records.length+1=N then _ else _)=_
  split
  · exact deferredDirection_eq_conjugacy _ _ _ a hz
  · rfl

/-- The actual deferred policy obeys the genuine observed-vector direction and stored-correction-span restrictions on all real histories.
Use: The actual deferred policy obeys the genuine observed-vector direction and stored-correction-span restrictions on all real histories.
Article: main_krylov, s3:def:DC and apB:lem:mu(d), genuine deferred-cancellation raw method.
Proof: Its real direction combines only the actual current gradient and true retained steps, and every genuine correction tree is empty. -/
theorem deferredMethod_spanRestricted (memory : ℕ → ℕ) (N : ℕ) (a : ℝ) :
    ProbedSpanRestricted memory (deferredMethod memory N a : ProbedMethod E) := by
  intro H
  refine ⟨?_,fun _ => trivial⟩
  change (if H.records.length+1=N then _ else _)∈H.observedSpan
  split
  · apply Submodule.add_mem
    · exact Submodule.neg_mem _ (History.gradient_mem_observedSpan H)
    · exact combine_mem _ _ (windowSteps_mem_observedSpan memory H) _
  · exact retained_direction_mem_observedSpan memory H
end
end krylov.Methods
