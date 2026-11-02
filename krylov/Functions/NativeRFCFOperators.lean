import krylov.Functions.NativeRFCFModel

/-!
Article: main_krylov, prop:Fcycle, the true RFC-F/operator dictionary.
Use: recover every actual retained value-model vector from the full genuine
ordinary-RFC execution. Only the final value-corrected inverse model changes;
the real old total steps and real observed gradient differences are retained.
Source: complete native history equality and the actual searched-segment
operator identity, followed by exact finite coordinate changes.
-/
namespace krylov.Functions
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Correction
open scoped InnerProductSpace Matrix Matrix.Norms.L2Operator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Equality of the true complete native histories identifies every actual
old total step with its original operator-executor step.
Article: main_krylov, prop:Fcycle, no fictitious line-step replacement. -/
theorem nativeRFC_record_step_of_prefix (T : E ≃L[ℝ] E) (f : E → ℝ) (G : E → E)
    (r : ℝ) (x₀ : E) (A B : ℕ → E →L[ℝ] E) (k : ℕ)
    (hp : ∀ j≤k, rfcFunctionRun T f G fullMemory r x₀ j=
      methodRun (rfcMethod fullMemory 1) A B (G x₀) j) :
    ∀ j<k, (rfcFunctionRecord T f G fullMemory r x₀
      (rfcFunctionRun T f G fullMemory r x₀ j)).step=
        probedStep (rfcMethod fullMemory 1) A B (G x₀) j := by
  intro j hj
  have he := congrArg (fun H : History E=>H.records.head?.map IterationRecord.step) (hp (j+1) (by omega))
  dsimp only [rfcFunctionRun,methodRun,methodAdvance] at he
  rw [hp j (by omega)] at he
  rw [hp j (by omega)]
  exact Option.some.inj he

/-- Actual native point differences are exactly the real old operator steps.
Article: main_krylov, prop:Fcycle, complete observed-pair dictionary. -/
theorem nativeRFC_point_step_of_prefix (T : E ≃L[ℝ] E) (f : E → ℝ) (G : E → E)
    (r : ℝ) (x₀ : E) (A B : ℕ → E →L[ℝ] E) (k : ℕ)
    (hp : ∀ j≤k, rfcFunctionRun T f G fullMemory r x₀ j=
      methodRun (rfcMethod fullMemory 1) A B (G x₀) j) :
    ∀ j<k, rfcFunctionPoint T f G fullMemory r x₀ (j+1)-rfcFunctionPoint T f G fullMemory r x₀ j=
      probedStep (rfcMethod fullMemory 1) A B (G x₀) j := by
  intro j hj
  rw [rfcFunctionPoint_succ,add_sub_cancel_left]
  exact nativeRFC_record_step_of_prefix T f G r x₀ A B k hp j hj

/-- Every actual retained gradient equals its genuine operator-executor observation.
Article: main_krylov, prop:Fcycle, full native oracle semantics. -/
theorem nativeRFC_point_gradient_of_prefix (T : E ≃L[ℝ] E) (f : E → ℝ) (G : E → E)
    (r : ℝ) (x₀ : E) (A B : ℕ → E →L[ℝ] E) (k : ℕ)
    (hp : ∀ j≤k, rfcFunctionRun T f G fullMemory r x₀ j=
      methodRun (rfcMethod fullMemory 1) A B (G x₀) j) :
    ∀ j≤k, G (rfcFunctionPoint T f G fullMemory r x₀ j)=
      probedGradient (rfcMethod fullMemory 1) A B (G x₀) j := by
  intro j hj
  rw [←rfcFunctionRun_gradient T f G fullMemory r x₀ j,hp j hj]
  rfl

/-- Reversing the actual retained steps gives the actual raw probed basis
with precisely its genuine current line-search column scale.
Article: main_krylov, prop:Fcycle, exact physical basis dictionary. -/
theorem nativeRFCF_steps_operator (T : E ≃L[ℝ] E) (f : E → ℝ) (G : E → E)
    (r : ℝ) (x₀ : E) (A B : ℕ → E →L[ℝ] E) (k : ℕ)
    (hp : ∀ j≤k, rfcFunctionRun T f G fullMemory r x₀ j=
      methodRun (rfcMethod fullMemory 1) A B (G x₀) j)
    (α : ℝ)
    (hs : rfcFunctionLineStep T f fullMemory r x₀ (rfcFunctionRun T f G fullMemory r x₀ k)=
      α • rfcFunctionDirection fullMemory (rfcFunctionRun T f G fullMemory r x₀ k)) :
    rfcFSteps T f G r x₀ k ∘ Fin.rev=
      rescaleWindow (probedStepBasis (rfcMethod fullMemory 1) A B (G x₀) k)
        (Fin.cons α (fun _=>1)) := by
  funext i
  refine Fin.cases ?_ (fun j=>?_) i
  · simp only [Function.comp_apply,Fin.rev_zero,rfcFSteps,Fin.val_last,lt_self_iff_false,ite_false,
      rescaleWindow,Fin.cons_zero,probedStepBasis]
    rw [hs,hp k (by omega)]
    rfl
  · have hj : j.succ.rev.val=k-1-j.val := by simp only [Fin.val_rev,Fin.val_succ]; omega
    have hlt : j.succ.rev.val<k := by rw [hj]; omega
    simp only [Function.comp_apply,rescaleWindow,probedStepBasis,Fin.cons_succ,one_smul]
    rw [rfcFSteps,ite_eq_left hlt]
    dsimp only [rfcFAnchors]
    rw [hj]
    exact nativeRFC_point_step_of_prefix T f G r x₀ A B k hp (k-1-j.val) (by omega)

/-- The actual retained observed secants have exactly the same raw-basis
coordinate scaling as their genuine actual total-step vectors.
Article: main_krylov, prop:Fcycle, complete secant/operator dictionary. -/
theorem nativeRFCF_images_operator (T : E ≃L[ℝ] E) (f : E → ℝ) (G : E → E)
    (r : ℝ) (x₀ : E) (A B : ℕ → E →L[ℝ] E) (k : ℕ)
    (hp : ∀ j≤k, rfcFunctionRun T f G fullMemory r x₀ j=
      methodRun (rfcMethod fullMemory 1) A B (G x₀) j)
    (α : ℝ)
    (hy : G (rfcFAnchor T f G r x₀ k)-G (rfcFunctionPoint T f G fullMemory r x₀ k)=
      α • A k (rfcFunctionDirection fullMemory (rfcFunctionRun T f G fullMemory r x₀ k))) :
    rfcFImages T f G r x₀ k ∘ Fin.rev=
      rescaleWindow (probedImageBasis (rfcMethod fullMemory 1) A B (G x₀) k)
        (Fin.cons α (fun _=>1)) := by
  funext i
  refine Fin.cases ?_ (fun j=>?_) i
  · simp only [Function.comp_apply,Fin.rev_zero,rescaleWindow,probedImageBasis,Fin.cons_zero]
    change G (rfcFAnchors T f G r x₀ k (Fin.last k)+rfcFSteps T f G r x₀ k (Fin.last k))-
      G (rfcFAnchors T f G r x₀ k (Fin.last k))=α • probedProbe (rfcMethod fullMemory 1) A B (G x₀) k
    rw [rfcFSteps_last_endpoint]
    change G (rfcFAnchor T f G r x₀ k)-G (rfcFunctionPoint T f G fullMemory r x₀ k)=_
    rw [hy,hp k (by omega)]
    rfl
  · have hj : j.succ.rev.val=k-1-j.val := by simp only [Fin.val_rev,Fin.val_succ]; omega
    have hlt : j.succ.rev.val<k := by rw [hj]; omega
    simp only [Function.comp_apply,rescaleWindow,probedImageBasis,Fin.cons_succ,one_smul]
    change G (rfcFAnchors T f G r x₀ k j.succ.rev+rfcFSteps T f G r x₀ k j.succ.rev)-
      G (rfcFAnchors T f G r x₀ k j.succ.rev)=probedSecant (rfcMethod fullMemory 1) A B (G x₀) (k-1-j.val)
    rw [rfcFSteps_old_endpoint T f G r x₀ k j.succ.rev hlt]
    dsimp only [rfcFAnchors]
    rw [hj,nativeRFC_point_gradient_of_prefix T f G r x₀ A B k hp (k-1-j.val+1) (by omega),
      nativeRFC_point_gradient_of_prefix T f G r x₀ A B k hp (k-1-j.val) (by omega)]
    rfl

/-- The real native RFC-F correction equals the true original modified raw
model solve on the complete unchanged ordinary-RFC prefix.
Article: main_krylov, prop:Fcycle, actual executor/source equivalence. -/
theorem rfcFCorrectionStep_modified_operator (T : E ≃L[ℝ] E) (f : E → ℝ) (G : E → E)
    (r : ℝ) (x₀ : E) (A B : ℕ → E →L[ℝ] E) (k : ℕ)
    (hp : ∀ j≤k, rfcFunctionRun T f G fullMemory r x₀ j=
      methodRun (rfcMethod fullMemory 1) A B (G x₀) j)
    (α : ℝ) (hα : α≠0)
    (hs : rfcFunctionLineStep T f fullMemory r x₀ (rfcFunctionRun T f G fullMemory r x₀ k)=
      α • rfcFunctionDirection fullMemory (rfcFunctionRun T f G fullMemory r x₀ k))
    (hy : G (rfcFAnchor T f G r x₀ k)-G (rfcFunctionPoint T f G fullMemory r x₀ k)=
      α • A k (rfcFunctionDirection fullMemory (rfcFunctionRun T f G fullMemory r x₀ k)))
    (hpost : G (rfcFAnchor T f G r x₀ k)=fullPostSearch 1 A B (G x₀) k)
    (hgate : rfcFunctionGate fullMemory (rfcFunctionRun T f G fullMemory r x₀ k)) :
    rfcFCorrectionStep T f G r x₀ k=
      rfcModifiedCorrection (k := k) A B (G x₀)
        (rfcFRawValueChange T f G r x₀ k (Fin.cons α (fun _=>1))) := by
  have hc : ∀ i : Fin (k+1), (Fin.cons α (fun _ : Fin k => (1 : ℝ)) : Fin (k+1) → ℝ) i≠0 := by
    intro i
    refine Fin.cases ?_ (fun _=>?_) i
    · exact hα
    · exact one_ne_zero
  have he := rfcFCorrectionStep_raw_model T f G r x₀ k
    (probedStepBasis (rfcMethod fullMemory 1) A B (G x₀) k)
    (probedImageBasis (rfcMethod fullMemory 1) A B (G x₀) k)
    (Fin.cons α (fun _=>1)) hc (nativeRFCF_steps_operator T f G r x₀ A B k hp α hs)
      (nativeRFCF_images_operator T f G r x₀ A B k hp α hy) hgate
  rw [hpost] at he
  exact he

end
end krylov.Functions
