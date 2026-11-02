import krylov.Cancellation.DCObserved
import krylov.Methods.EmptyCompilation
import krylov.Methods.ReferenceModels
import krylov.Methods.SmoothTrace
set_option autoImplicit false
/-!
Article: main_krylov, thm:dcs(c), actual primitive DC-slide smooth cycle dictionary.
Use: place the original data-dependent estimate implementation in the genuine
local smooth source class and derive actual executed-gradient regularity.
Source: original observed DC coefficient synthesis, reused empty-correction
compiler, real FC quadratic history and true retained positive reference models.
-/

namespace krylov.Cancellation
noncomputable section
open krylov.Methods krylov.Reference krylov.Stability
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Primitive smooth positive observed estimates give the original actual
DC-slide executor a genuine C-r local finite coefficient representation.
Use: the source smooth-cycle hypothesis is proved from the real estimate
rule and true quadratic reference domains, without a trajectory/response field.
Article: main_krylov, thm:dcs(c) and lem:U(d).
Proof: compile the genuine observed tilted direction with the existing empty
correction program. Actual quadratic DC-slide histories are the true FC
histories, whose retained conjugacy models are positive. The original estimate
chart supplies precisely its actual scalar inverse domain and C-r coefficients. -/
theorem dc_slide_smoothCycleAt (memory : ℕ → ℕ) (hm : ∀ k,0<k → 0<memory k)
    (estimate : History E → ℝ) (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E,v≠0 → 0 < inner ℝ v (Q v)) (g : E) (N : ℕ)
    (hpre : ∀ k<N,CG.gradient Q g k≠0) (r : WithTop ℕ∞)
    (ha : ∀ k<N,
      let H := methodRun (dcSlideMethod memory estimate) (fun _ => Q) (fun _ => Q) g k
      ContDiffAt ℝ r (historyEstimateChart estimate H.queryShape H.observationList.length)
        (observedArray H.observationList.length H.observationList))
    (ha0 : ∀ k<N,0<estimate (methodRun (dcSlideMethod memory estimate) (fun _ => Q) (fun _ => Q) g k)) :
    SmoothProbedCycleAt (dcSlideMethod memory estimate) r Q g N := by
  apply emptyCompiled_smoothCycleAt (dcSlideMethod memory estimate) (fun _ _ => rfl)
    (dcObservedRule memory estimate) (fun shape n data => dcObservedRule_evaluate memory estimate shape data) Q g N r
  intro k hk
  apply dcObserved_actual_regular memory estimate _ r _ (ha k hk) (ha0 k hk).ne'
  have hW : selectedWindow memory (methodRun (dcSlideMethod memory estimate) (fun _ => Q) (fun _ => Q) g k)=
      (referencePairs Q g k).take (memory k) := by
    rw [dc_slide_reference_run memory hm estimate Q hQ hpos g k]
    unfold selectedWindow
    rw [methodRun_length,(fcMethod_static memory Q hQ hpos g (fun i _ => hm i) k).2]
  rw [hW]
  exact (retainedConjugacy_posDef Q hQ hpos g k (memory k) (fun i hi => hpre i (hi.trans hk))).det_pos.ne'

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The true varying-prefix DC-slide returned gradient is C-r from original
primitive operator data and smooth positive observed estimate charts.
Use: actual cancellation linearization and compact estimates receive genuine
executed regularity instead of assuming it for a desired trajectory.
Article: main_krylov, thm:dcs(c) and lem:U(d).
Proof: the real primitive coefficient dictionary proves actual smooth-cycle
membership, and the existing genuine CG-consistent finite execution calculus
transfers that representation to the original returned-gradient cycle. -/
theorem dc_slide_gradient_contDiffAt (memory : ℕ → ℕ) (hm : ∀ k,0<k → 0<memory k)
    (estimate : History E → ℝ) (A B : X → ℕ → E →L[ℝ] E) (g : X → E) (x : X) (N : ℕ) {r : WithTop ℕ∞}
    (hA : ∀ k<N,ContDiffAt ℝ r (fun p => A p k) x)
    (hB : ∀ k<N,ContDiffAt ℝ r (fun p => B p k) x) (hg : ContDiffAt ℝ r g x)
    (Q : E →L[ℝ] E) (hAx : A x=fun _ => Q) (hBx : B x=fun _ => Q)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E,v≠0 → 0 < inner ℝ v (Q v))
    (hpre : ∀ k<N,CG.gradient Q (g x) k≠0)
    (ha : ∀ k<N,
      let H := methodRun (dcSlideMethod memory estimate) (fun _ => Q) (fun _ => Q) (g x) k
      ContDiffAt ℝ r (historyEstimateChart estimate H.queryShape H.observationList.length)
        (observedArray H.observationList.length H.observationList))
    (ha0 : ∀ k<N,0<estimate (methodRun (dcSlideMethod memory estimate) (fun _ => Q) (fun _ => Q) (g x) k)) :
    ContDiffAt ℝ r (fun p => (methodRun (dcSlideMethod memory estimate) (A p) (B p) (g p) N).gradient) x :=
  smoothProbed_gradient_regular _ (dc_slide_consistent memory hm estimate) A B g x N hA hB hg Q hAx hBx hQ hpos hpre
    (dc_slide_smoothCycleAt memory hm estimate Q hQ hpos (g x) N hpre r ha ha0)

end
end krylov.Cancellation
