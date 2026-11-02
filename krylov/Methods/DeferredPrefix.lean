import krylov.Methods.DeferredSmoothClass
import krylov.Methods.CorrectionFreeOracles

set_option autoImplicit false
/-!
Article: main_krylov, s3:def:DC and apB:lem:mu(d), actual deferred prefix and reference directions.
Use: preserve every genuine pre-final FC observation and identify the
true deferred current quadratic direction with the actual CG direction.
Source: real horizon-selected raw decisions, genuine complete-history
execution and proved actual deferred/FC quadratic transcript equality.
-/

namespace krylov.Methods
noncomputable section
open krylov.Reference
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The genuine deferred method preserves the complete actual FC history before its designated final iteration for every true operator sequence.
Use: The genuine deferred method preserves the complete actual FC history before its designated final iteration for every true operator sequence.
Article: main_krylov, s3:def:DC and apB:lem:mu(d), actual deferred prefix and reference directions.
Proof: Every real earlier horizon branch chooses actual FC and both genuine correction phases are empty. -/
theorem deferredMethod_run_before (memory : ℕ → ℕ) (N : ℕ) (a : ℝ)
    (A B : ℕ → E →L[ℝ] E) (g : E) (k : ℕ) (hk : k<N) :
    methodRun (deferredMethod memory N a) A B g k=methodRun (fcMethod memory) A B g k := by
  -- Preserve the actual full observed history through every genuine earlier horizon branch.
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [methodRun,methodRun,ih (by omega)]
    unfold methodAdvance
    have hd : (deferredMethod memory N a).direction (methodRun (fcMethod memory) A B g k)=
        (fcMethod memory).direction (methodRun (fcMethod memory) A B g k) := by
      simp only [deferredMethod,methodRun_length,show ¬ k+1=N by omega,ite_false]
    rw [hd]
    rfl

/-- Every genuine earlier recorded deferred step equals the true FC step on arbitrary actual operator data.
Use: Every genuine earlier recorded deferred step equals the true FC step on arbitrary actual operator data.
Article: main_krylov, s3:def:DC and apB:lem:mu(d), actual deferred prefix and reference directions.
Proof: Read the true recorded-step observation from the genuine identical complete earlier histories. -/
theorem deferredMethod_step_before (memory : ℕ → ℕ) (N : ℕ) (a : ℝ)
    (A B : ℕ → E →L[ℝ] E) (g : E) (i : ℕ) (hi : i+1<N) :
    probedStep (deferredMethod memory N a) A B g i=probedStep (fcMethod memory) A B g i :=
  congrArg (fun H : History E => H.observationList.getD 4 0)
    (deferredMethod_run_before memory N a A B g (i+1) hi)

/-- The genuine deferred current direction is exactly the actual CG direction on every true positive quadratic, including solved tails.
Use: The genuine deferred current direction is exactly the actual CG direction on every true positive quadratic, including solved tails.
Article: main_krylov, s3:def:DC and apB:lem:mu(d), actual deferred prefix and reference directions.
Proof: Its actual full reference transcript is FC and the genuine old-step residual coordinates vanish, so the true deferred solve reduces to real FC. -/
theorem deferredMethod_reference_direction (memory : ℕ → ℕ) (hm : ∀ k, 0<k → 0<memory k)
    (N : ℕ) (a : ℝ) (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v)) (g : E) (k : ℕ) :
    probedDirection (deferredMethod memory N a) (fun _ => Q) (fun _ => Q) g k=CG.direction Q g k := by
  unfold probedDirection
  rw [deferredMethod_reference_run memory hm N a Q hQ hpos g k]
  have hs := fcMethod_static memory Q hQ hpos g (fun i _ => hm i) k
  have hz := history_reference_coordinates_zero Q hQ hpos g k _ hs.2 hs.1 memory
  rw [deferredMethod_direction_eq_FC memory N a _ hz]
  exact retainedMethod_direction memory (fun _ _ => .done) Q hQ hpos g k _ hs.1 hs.2 (fun _ => hm k)
end
end krylov.Methods
