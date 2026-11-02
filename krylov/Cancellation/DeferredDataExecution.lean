import krylov.Cancellation.DeferredDataReference
import krylov.Cancellation.ResidualPropagation
set_option autoImplicit false
/-!
Article: main_krylov, thm:DC, genuine data-dependent deferred execution identities.
Use: keep every actual pre-final FC observation and read the exact native
last residual transfer with the original observed final estimate.
Source: real horizon-selected execution, native observed tilted equations
and the already proved actual finite scalar residual identity.
-/

namespace krylov.Cancellation
noncomputable section
open krylov.Methods krylov.Reference
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Every actual data-dependent deferred pre-final history is exactly the
original FC history on arbitrary true operator data.
Use: arbitrary observed final estimates cannot change earlier observed inputs.
Article: main_krylov, thm:DC.
Proof: induct through real execution; every genuinely earlier horizon branch
selects the original FC direction, and both correction programs are empty. -/
theorem deferred_data_run_before (memory : ℕ → ℕ) (N : ℕ) (estimate : History E → ℝ)
    (A B : ℕ → E →L[ℝ] E) (g : E) (k : ℕ) (hk : k<N) :
    methodRun (deferredDataMethod memory N estimate) A B g k=methodRun (fcMethod memory) A B g k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [methodRun,methodRun,ih (by omega)]
    unfold methodAdvance
    have hd : (deferredDataMethod memory N estimate).direction (methodRun (fcMethod memory) A B g k)=
        (fcMethod memory).direction (methodRun (fcMethod memory) A B g k) := by
      simp only [deferredDataMethod,methodRun_length,show ¬ k+1=N by omega,ite_false]
    rw [hd]
    rfl

/-- Every real earlier recorded step of the observed-estimate deferred method
is exactly its original FC recorded step.
Use: the final cancellation derivative uses the genuine prior FC residual.
Article: main_krylov, thm:DC.
Proof: read the actual latest recorded step from the proved full pre-final history equality. -/
theorem deferred_data_step_before (memory : ℕ → ℕ) (N : ℕ) (estimate : History E → ℝ)
    (A B : ℕ → E →L[ℝ] E) (g : E) (i : ℕ) (hi : i+1<N) :
    probedStep (deferredDataMethod memory N estimate) A B g i=probedStep (fcMethod memory) A B g i :=
  congrArg (fun H : History E => H.observationList.getD 4 0)
    (deferred_data_run_before memory N estimate A B g (i+1) hi)

/-- The genuine final data-dependent deferred direction is the true CG
reference direction, including all solved tails.
Use: identify the actual reference searched line before taking first variations.
Article: main_krylov, thm:DC.
Proof: genuine global quadratic history equality and the true zero old
residual identify the original horizon-selected decision with native FC. -/
theorem deferred_data_quadratic_direction (memory : ℕ → ℕ) (hm : ∀ k,0<k → 0<memory k)
    (N : ℕ) (estimate : History E → ℝ) (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E,v≠0 → 0 < inner ℝ v (Q v)) (g : E) (k : ℕ) :
    probedDirection (deferredDataMethod memory N estimate) (fun _ => Q) (fun _ => Q) g k=CG.direction Q g k := by
  unfold probedDirection
  rw [deferred_data_reference_run memory hm N estimate Q hQ hpos g k]
  have hs := fcMethod_static memory Q hQ hpos g (fun j _ => hm j) k
  rw [deferred_data_reference_direction memory N estimate Q hQ hpos g k _ hs.2 hs.1]
  exact retainedMethod_direction memory (fun _ _ => .done) Q hQ hpos g k _ hs.1 hs.2 (fun _ => hm k)

/-- Every actual old-step/final-gradient residual of data-dependent deferred
cancellation equals its true physical fresh defect plus the genuine old
residual multiplied by the original observed-estimate damping factor.
Use: differentiate the actual original DC executor, including the arbitrary
smooth final estimate read on its real pre-final observed history.
Article: main_krylov, thm:DC.
Proof: locate the real old retained pair, read its actual tilted native
conjugacy equation and substitute the real empty-correction search and secant
into the proved genuine scalar residual-transfer identity. -/
theorem deferred_data_last_residual (estimate : History E → ℝ)
    (A B : ℕ → E →L[ℝ] E) (g : E) (k i : ℕ) (hi : i<k)
    (hAi : (A i).toLinearMap.IsSymmetric)
    (hdet : IsUnit (crossGram
      (windowImages (selectedWindow fullMemory (methodRun (deferredDataMethod fullMemory (k+1) estimate) A B g k)))
      (windowSteps (selectedWindow fullMemory (methodRun (deferredDataMethod fullMemory (k+1) estimate) A B g k)))).det) :
    let m := deferredDataMethod fullMemory (k+1) estimate
    let H := methodRun m A B g k
    let alpha := lineLength (probedGradient m A B g k) (probedDirection m A B g k) (probedProbe m A B g k)
    inner ℝ (probedStep m A B g i) (probedGradient m A B g (k+1))=
      (1-alpha/estimate H)*inner ℝ (probedStep m A B g i) (probedGradient m A B g k)+
        inner ℝ (probedStep m A B g i) ((A k-A i) (probedStep m A B g k)) := by
  let m := deferredDataMethod fullMemory (k+1) estimate
  let H := methodRun m A B g k
  let W := selectedWindow fullMemory H
  have hm : CorrectionFree m := fun _ _ => rfl
  have hmem := probed_pair_retained m fullMemory A B g k i hi (by change k-1-i<k;omega)
  obtain ⟨j,hj,hget⟩ := List.mem_iff_getElem.mp hmem
  have hx : windowSteps W ⟨j,hj⟩=probedStep m A B g i := congrArg Prod.fst hget
  have hy : windowImages W ⟨j,hj⟩=probedSecant m A B g i := congrArg Prod.snd hget
  have hd : probedDirection m A B g k=
      deferredDirection (windowSteps W) (windowImages W) H.gradient (estimate H) := by
    change (if H.records.length+1=k+1 then _ else _)=_
    rw [ite_eq_left (by rw [methodRun_length])]
    rfl
  have hp := deferredDirection_conjugacy (windowSteps W) (windowImages W) H.gradient (estimate H) hdet ⟨j,hj⟩
  rw [hx,hy,correctionFree_secant m hm,← hd] at hp
  dsimp only
  rw [correctionFree_gradient_succ m hm A B g k,correctionFree_step m hm A B g k]
  exact tilted_residual_identity (A i) (A k) hAi _ _ _ _ _ hp

end
end krylov.Cancellation
