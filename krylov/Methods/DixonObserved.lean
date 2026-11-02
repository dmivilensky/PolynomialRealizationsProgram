import krylov.Methods.RecordedPrediction
import krylov.Methods.LBFGS
set_option autoImplicit false
/-!
Article: main_krylov, prop:classical(a,b), original observed Dixon implementations.
Use: execute predicted-gradient conjugate gradients and identity-initialized
BFGS from the actual observed point/gradient correction formulas.
Source: main_krylov's Dixon73/Dixon75 Section 3 dictionary, standard
Fletcher--Reeves recurrence and the existing genuine BFGS two-loop update. -/

namespace krylov.Methods
noncomputable section
open krylov.Reference
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Dixon's predicted-gradient Fletcher--Reeves direction, with the actual
previous queried direction reconstructed from its real step and old trial.
Use: the observed predictor and old direction are actual data-only quantities;
no true CG gradient or hidden matrix action is supplied to this implementation.
Article: main_krylov, prop:classical(a), Dixon75 Section 3. -/
def dixonFRDirection (trial : History E → ℝ) (H : History E) : E :=
  -recordedPredictedGradient H+
    (‖recordedPredictedGradient H‖^2/‖recordedPredictedGradient (historyTail H)‖^2) • measuredTrialDirection trial H

/-- The genuine predicted-gradient Dixon CG one-gradient implementation.
Use: real evaluated trials launch from the actual evaluated point and the
literal recorded point correction is applied only at the unevaluated output.
Article: main_krylov, prop:classical(a,b), Dixon75 Section 3. -/
def dixonCGMethod (trial : History E → ℝ) : OneGradientMethod E where
  step H := trial H • dixonFRDirection trial H
  output H := recordedProjectionCorrection H

/-- The genuine predicted-gradient Dixon BFGS one-gradient implementation
with original identity initial inverse metric and real full measured pairs.
Use: the final correction is the actual accumulated BFGS inverse action on
the real evaluated gradient; no latest-model output is substituted for it.
Article: main_krylov, prop:classical(a,b,c), Dixon73 with BFGS and H0=I. -/
def dixonBFGSMethod (trial : History E → ℝ) : OneGradientMethod E where
  step H := trial H • (-inverseBFGSApply 1 H.pairs (recordedPredictedGradient H))
  output H := -inverseBFGSApply 1 H.pairs H.gradient

/-- The actual predicted-gradient Fletcher--Reeves direction lies in the
true observed span on every supplied complete history.
Use: the named Dixon CG implementation has genuine source admissibility.
Article: main_krylov, prop:classical and def:classes(M1).
Proof: its true predictor and reconstructed previous direction are proved
available observations; the scalar coefficient uses only their actual data. -/
theorem dixonFRDirection_mem_observedSpan (trial : History E → ℝ) (H : History E) :
    dixonFRDirection trial H∈H.observedSpan := by
  exact H.observedSpan.add_mem (H.observedSpan.neg_mem (recordedPredictedGradient_mem_observedSpan H))
    (H.observedSpan.smul_mem _ (measuredTrialDirection_mem_observedSpan trial H))

/-- The actual predicted-gradient Dixon CG executor is span restricted on
all supplied histories, without positivity or quadratic premises.
Use: the named method belongs to the genuine one-gradient source class.
Article: main_krylov, prop:classical and def:classes(M1).
Proof: the real trial only scales its proved available predicted-gradient direction. -/
theorem dixonCGMethod_spanRestricted (trial : History E → ℝ) : OneGradientSpanRestricted (dixonCGMethod trial) :=
  fun H => H.observedSpan.smul_mem _ (dixonFRDirection_mem_observedSpan trial H)

/-- The actual identity-initialized predicted-gradient Dixon BFGS executor
is span restricted on every supplied complete history.
Use: the original full quasi-Newton implementation has source admissibility
from its real observed-pair recursion, without an inverse-model class field.
Article: main_krylov, prop:classical and def:classes(M1).
Proof: the genuine two-loop inverse action stays in the span of its actual
input and real pair vectors, all proved genuine observed generators. -/
theorem dixonBFGSMethod_spanRestricted (trial : History E → ℝ) :
    OneGradientSpanRestricted (dixonBFGSMethod trial) := by
  intro H
  apply H.observedSpan.smul_mem
  apply H.observedSpan.neg_mem
  apply inverseBFGSApply_mem
  · intro p hp
    constructor
    · exact Submodule.subset_span (Or.inl (Or.inl (Or.inr ⟨p,hp,rfl⟩)))
    · exact Submodule.subset_span (Or.inl (Or.inr ⟨p,hp,rfl⟩))
  · exact recordedPredictedGradient_mem_observedSpan H

end
end krylov.Methods
