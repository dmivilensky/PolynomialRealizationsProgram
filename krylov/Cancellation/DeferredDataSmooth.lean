import krylov.Cancellation.DeferredDataObserved
import krylov.Methods.EmptyCompilation
import krylov.Methods.ReferenceModels
set_option autoImplicit false
/-!
Article: main_krylov, s3:def:DC and thm:DC, original smooth data-dependent deferred executor.
Use: derive genuine native cycle regularity from the primitive observed final
estimate only where the original deferred policy actually reads it.
Source: true finite horizon compiler, genuine arbitrary-estimate quadratic
FC history, retained positive reference models and existing raw execution calculus.
-/

namespace krylov.Cancellation
noncomputable section
open krylov.Methods krylov.Reference krylov.Stability
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The original actual final-estimate deferred policy has genuine C-r native
smooth-cycle representation from its primitive smooth positive observed estimate.
Use: the source's data-dependent estimate is neither frozen nor replaced by a
smooth-trajectory hypothesis; FC prefix iterations require no unread estimate regularity.
Article: main_krylov, s3:def:DC and thm:DC.
Proof: compile the real horizon-selected observed rule with no corrections.
Actual quadratic reference histories are FC for every estimate, so all true
retained matrix domains are positive. The original estimate hypotheses apply
only on the actual final branch in the genuine finite observed chart. -/
theorem deferred_data_smoothCycleAt (memory : ℕ → ℕ) (hm : ∀ k,0<k → 0<memory k)
    (horizon : ℕ) (estimate : History E → ℝ) (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E,v≠0 → 0 < inner ℝ v (Q v)) (g : E) (N : ℕ)
    (hpre : ∀ k<N,CG.gradient Q g k≠0) (r : WithTop ℕ∞)
    (ha : ∀ k<N,k+1=horizon →
      let H := methodRun (deferredDataMethod memory horizon estimate) (fun _ => Q) (fun _ => Q) g k
      ContDiffAt ℝ r (historyEstimateChart estimate H.queryShape H.observationList.length)
        (observedArray H.observationList.length H.observationList))
    (ha0 : ∀ k<N,k+1=horizon →
      0<estimate (methodRun (deferredDataMethod memory horizon estimate) (fun _ => Q) (fun _ => Q) g k)) :
    SmoothProbedCycleAt (deferredDataMethod memory horizon estimate) r Q g N := by
  apply emptyCompiled_smoothCycleAt (deferredDataMethod memory horizon estimate) (fun _ _ => rfl)
    (deferredDataObservedRule memory horizon estimate) (deferredDataObservedRule_evaluate memory horizon estimate) Q g N r
  intro k hk
  apply deferredDataObserved_actual_regular memory horizon estimate _ r
  · have hW : selectedWindow memory (methodRun (deferredDataMethod memory horizon estimate) (fun _ => Q) (fun _ => Q) g k)=
        (referencePairs Q g k).take (memory k) := by
      rw [deferred_data_reference_run memory hm horizon estimate Q hQ hpos g k]
      unfold selectedWindow
      rw [methodRun_length,(fcMethod_static memory Q hQ hpos g (fun i _ => hm i) k).2]
    rw [hW]
    exact (retainedConjugacy_posDef Q hQ hpos g k (memory k) (fun i hi => hpre i (hi.trans hk))).det_pos.ne'
  · intro hbranch
    exact ha k hk (by simpa only [methodRun_length] using hbranch)
  · intro hbranch
    exact (ha0 k hk (by simpa only [methodRun_length] using hbranch)).ne'

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The original actually executed data-dependent deferred returned gradient
is C-r under primitive operator data and true final observed-estimate regularity.
Use: source first variations and compact remainders apply to the genuine
native final solve, not to a constant-estimate surrogate.
Article: main_krylov, s3:def:DC, thm:DC and lem:U(d).
Proof: real primitive coefficient compilation proves the original smooth-cycle
representation and actual global quadratic consistency; the existing true raw
execution theorem gives the original returned-gradient regularity. -/
theorem deferred_data_gradient_contDiffAt (memory : ℕ → ℕ) (hm : ∀ k,0<k → 0<memory k)
    (horizon : ℕ) (estimate : History E → ℝ) (A B : X → ℕ → E →L[ℝ] E) (g : X → E) (x : X) (N : ℕ) {r : WithTop ℕ∞}
    (hA : ∀ k<N,ContDiffAt ℝ r (fun p => A p k) x)
    (hB : ∀ k<N,ContDiffAt ℝ r (fun p => B p k) x) (hg : ContDiffAt ℝ r g x)
    (Q : E →L[ℝ] E) (hAx : A x=fun _ => Q) (hBx : B x=fun _ => Q)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E,v≠0 → 0 < inner ℝ v (Q v))
    (hpre : ∀ k<N,CG.gradient Q (g x) k≠0)
    (ha : ∀ k<N,k+1=horizon →
      let H := methodRun (deferredDataMethod memory horizon estimate) (fun _ => Q) (fun _ => Q) (g x) k
      ContDiffAt ℝ r (historyEstimateChart estimate H.queryShape H.observationList.length)
        (observedArray H.observationList.length H.observationList))
    (ha0 : ∀ k<N,k+1=horizon →
      0<estimate (methodRun (deferredDataMethod memory horizon estimate) (fun _ => Q) (fun _ => Q) (g x) k)) :
    ContDiffAt ℝ r (fun p => (methodRun (deferredDataMethod memory horizon estimate) (A p) (B p) (g p) N).gradient) x :=
  smoothProbed_gradient_regular _ (deferred_data_consistent memory hm horizon estimate) A B g x N hA hB hg Q hAx hBx hQ hpos hpre
    (deferred_data_smoothCycleAt memory hm horizon estimate Q hQ hpos (g x) N hpre r ha ha0)

end
end krylov.Cancellation
