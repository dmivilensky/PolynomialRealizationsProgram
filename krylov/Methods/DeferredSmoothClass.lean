import krylov.Methods.DeferredCompilation
import krylov.Methods.ReferenceModels

set_option autoImplicit false
/-!
Article: main_krylov, s3:def:DC and apB:lem:mu(d), actual primitive smooth deferred source class.
Use: place the genuine deferred-cancellation implementation in the true
smooth globally CG-consistent information class with actual coefficient domains.
Source: proved real deferred quadratic execution, actual retained positive
conjugacy models and genuine empty-correction primitive policy compilation.
-/

namespace krylov.Methods
noncomputable section
open krylov.Reference krylov.Stability
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The genuine deferred raw method has an actual primitive C-r local observed-program representation on every true nonstagnating positive quadratic cycle.
Use: The genuine deferred raw method has an actual primitive C-r local observed-program representation on every true nonstagnating positive quadratic cycle.
Article: main_krylov, s3:def:DC and apB:lem:mu(d), actual primitive smooth deferred source class.
Proof: Compile the real empty-correction policy with the actual observed deferred/FC rule. Its genuine complete quadratic history is FC, so true retained conjugacy positivity derives every actual primitive inverse domain. -/
theorem deferredMethod_smoothCycleAt (memory : ℕ → ℕ) (hm : ∀ k, 0<k → 0<memory k)
    (horizon : ℕ) (a : ℝ) (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v)) (g : E) (N : ℕ)
    (hpre : ∀ k<N, CG.gradient Q g k≠0) (r : WithTop ℕ∞) :
    SmoothProbedCycleAt (deferredMethod memory horizon a) r Q g N := by
  -- Compile the genuine actual raw decisions before deriving their true reference inverse domains from real quadratic histories.
  apply emptyCompiled_smoothCycleAt (deferredMethod memory horizon a) (fun _ _ => rfl)
    (deferredMethodObservedRule memory horizon a) (deferredMethodObservedRule_evaluate memory horizon a) Q g N r
  intro k hk
  apply deferredMethodObserved_actual_regular memory horizon a _ r
  have hW : selectedWindow memory (methodRun (deferredMethod memory horizon a) (fun _ => Q) (fun _ => Q) g k)=
      (referencePairs Q g k).take (memory k) := by
    rw [deferredMethod_reference_run memory hm horizon a Q hQ hpos g k]
    unfold selectedWindow
    rw [methodRun_length,(fcMethod_static memory Q hQ hpos g (fun i _ => hm i) k).2]
  rw [hW]
  exact (retainedConjugacy_posDef Q hQ hpos g k (memory k) (fun i hi => hpre i (hi.trans hk))).det_pos.ne'

/-- The actual deferred-cancellation implementation as a genuine primitive smooth globally CG-consistent source-class member.
Use: The actual deferred-cancellation implementation as a genuine primitive smooth globally CG-consistent source-class member.
Article: main_krylov, s3:def:DC and apB:lem:mu(d), actual primitive smooth deferred source class.
Proof: Combine its real all-history span restriction, true global quadratic consistency and genuine primitive finite coefficient representation. -/
def smoothDeferredClass (memory : ℕ → ℕ) (hm : ∀ k, 0<k → 0<memory k) (N : ℕ) (a : ℝ) : SmoothProbedClass E where
  memory := memory
  policy := deferredMethod memory N a
  admissible := deferredMethod_spanRestricted memory N a
  consistent := deferredMethod_consistent memory hm N a
  smooth := fun Q hQ hpos g L hpre => deferredMethod_smoothCycleAt memory hm N a Q hQ hpos g L hpre 2
end
end krylov.Methods
