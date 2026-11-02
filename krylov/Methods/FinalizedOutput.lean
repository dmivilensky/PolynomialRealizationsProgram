import krylov.Methods.FinalizedSmoothClass
import krylov.Methods.SmoothProbedFields

set_option autoImplicit false
/-!
Article: main_krylov, thm:select and apB:lem:mu(a), actual final-wrapper output identities.
Use: identify genuine earlier recorded steps, the actual final search
direction and the real returned final gradient of the appended latest-model
wrapper on arbitrary true line and correction operator sequences.
Source: exact genuine prefix execution and actual correction-tree
continuation with its true returned-gradient semantics.
-/

namespace krylov.Methods
noncomputable section
open krylov.Reference
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual final wrapper preserves every genuine earlier recorded step before its designated last iteration.
Use: The actual final wrapper preserves every genuine earlier recorded step before its designated last iteration.
Article: main_krylov, thm:select and apB:lem:mu(a), actual final-wrapper output identities.
Proof: Read the actual recorded-step coordinate from the true identical earlier complete histories. -/
theorem finalizedMethod_step_before (m : ProbedMethod E) (N : ℕ)
    (A B : ℕ → E →L[ℝ] E) (g : E) (k : ℕ) (hk : k+1<N) :
    probedStep (finalizedMethod m N) A B g k=probedStep m A B g k :=
  congrArg (fun H : History E => H.observationList.getD 4 0) (finalizedMethod_run_before m N A B g (k+1) hk)

/-- The actual final wrapper uses exactly the genuine original search direction at its designated last iteration.
Use: The actual final wrapper uses exactly the genuine original search direction at its designated last iteration.
Article: main_krylov, thm:select and apB:lem:mu(a), actual final-wrapper output identities.
Proof: Its true prior complete history is unchanged and its actual direction branch remains the genuine original policy. -/
theorem finalizedMethod_direction_last (m : ProbedMethod E)
    (A B : ℕ → E →L[ℝ] E) (g : E) (k : ℕ) :
    probedDirection (finalizedMethod m (k+1)) A B g k=probedDirection m A B g k := by
  unfold probedDirection
  rw [finalizedMethod_run_before m (k+1) A B g k (by omega)]
  exact finalizedMethod_direction_before m (k+1) _ (by rw [methodRun_length];omega)

/-- The actual final wrapper returns precisely the true one-model-correction gradient applied to the real original final gradient, on every genuine operator sequence.
Use: The actual final wrapper returns precisely the true one-model-correction gradient applied to the real original final gradient, on every genuine operator sequence.
Article: main_krylov, thm:select and apB:lem:mu(a), actual final-wrapper output identities.
Proof: Identify the actual unchanged prior history and genuine original final search, then use real correction-tree continuation to start the actual latest-model solve at the true gradient returned by the original phase. -/
theorem finalizedMethod_gradient_last (m : ProbedMethod E)
    (A B : ℕ → E →L[ℝ] E) (g : E) (k : ℕ) :
    probedGradient (finalizedMethod m (k+1)) A B g (k+1)=
      (runCorrections (latestAfter m (methodRun m A B g k) (probedProbe m A B g k)
        (probedGradient m A B g (k+1))) (B k) (probedGradient m A B g (k+1))).gradient := by
  -- Execute the genuine original correction tree first, retaining its actual returned gradient before the real appended model solve begins.
  rw [probedGradient_succ]
  unfold probedPhase
  rw [finalizedMethod_run_before m (k+1) A B g k (by omega)]
  dsimp only
  rw [finalizedMethod_direction_before m (k+1) _ (by rw [methodRun_length];omega)]
  change (runCorrections (if (methodRun m A B g k).records.length+1=k+1 then _ else _) (B k) _).gradient=_
  rw [methodRun_length,ite_eq_left rfl]
  exact (CorrectionTree.run_follow (m.correction _ _) (latestAfter m _ _) (B k) _).2.1
end
end krylov.Methods
