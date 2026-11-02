import krylov.Cancellation.DCObserved
import krylov.Cancellation.DeferredDataReference
set_option autoImplicit false
/-!
Article: main_krylov, s3:def:DC and thm:DC, original data-dependent final estimate compiler.
Use: compile the actual final observed estimate and FC prefix into genuine
primitive observed coefficients, requiring smooth estimate data only at the
source's single true deferred horizon.
Source: real observed DC/FC rules, genuine history reconstruction and actual
native finite-array/list inverse-solve coordinate invariance.
-/

namespace krylov.Cancellation
noncomputable section
open krylov.Methods krylov.Reference krylov.Stability
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The original final-horizon branch of genuine observed deferred coefficients.
Use: earlier actual iterations use the reused FC observed rule directly.
Article: main_krylov, s3:def:DC and thm:DC. -/
def deferredDataObservedRule (memory : ℕ → ℕ) (horizon : ℕ) (estimate : History E → ℝ)
    (shape : List ℕ) (n : ℕ) : ObservedRule E n :=
  if shape.length+1=horizon then dcObservedRule memory estimate shape n else fcObservedRule memory shape n

/-- The actual horizon-selected primitive coefficients evaluate exactly to
the genuine original data-dependent deferred implementation.
Use: this compiler preserves the real decision before any new operator action.
Article: main_krylov, s3:def:DC and thm:DC.
Proof: the original fixed observation shape gives its true record count;
use the proved actual DC observed synthesis or the reused exact FC dictionary. -/
theorem deferredDataObservedRule_evaluate (memory : ℕ → ℕ) (horizon : ℕ) (estimate : History E → ℝ)
    (shape : List ℕ) (n : ℕ) (data : Fin n → E) :
    (deferredDataObservedRule memory horizon estimate shape n).evaluate data=
      (deferredDataMethod memory horizon estimate).direction (historyFromObservations shape (List.ofFn data)) := by
  by_cases hc : shape.length+1=horizon
  · simp only [deferredDataObservedRule,deferredDataMethod,historyFromObservations_records_length,hc,ite_true]
    exact dcObservedRule_evaluate memory estimate shape data
  · simp only [deferredDataObservedRule,deferredDataMethod,historyFromObservations_records_length,hc,ite_false]
    exact fcObservedRule_evaluate memory shape data

/-- The true final-estimate primitive coefficients are C-r from original
smooth nonzero estimate data on the genuine deferred branch only.
Use: earlier FC iterations require no unused regularity assumption on the
unread data-only final estimate.
Article: main_krylov, s3:def:DC and thm:DC.
Proof: the actual fixed horizon selects the proved genuine data-dependent
DC coefficient calculus or the existing primitive FC coefficient calculus. -/
theorem deferredDataObservedRule_coefficient_regular (memory : ℕ → ℕ) (horizon : ℕ)
    (estimate : History E → ℝ) (shape : List ℕ) (n : ℕ) (data : Fin n → E) (r : WithTop ℕ∞)
    (hC : (crossGram (chartImages memory shape data) (chartSteps memory shape data)).det≠0)
    (ha : shape.length+1=horizon → ContDiffAt ℝ r (historyEstimateChart estimate shape n) data)
    (ha0 : shape.length+1=horizon → historyEstimateChart estimate shape n data≠0) :
    ContDiffAt ℝ r (deferredDataObservedRule memory horizon estimate shape n).coefficient data := by
  by_cases hc : shape.length+1=horizon
  · simp only [deferredDataObservedRule,hc,ite_true]
    exact dcObservedRule_coefficient_regular memory estimate shape data r hC (ha hc) (ha0 hc)
  · simp only [deferredDataObservedRule,hc,ite_false]
    exact fcObservedRule_coefficient_regular memory shape data hC r

/-- Original primitive final-estimate regularity gives actual native deferred
coefficient regularity at real histories with genuine retained inverse domains.
Use: transfer the original data-only source hypothesis to its true finite compiler.
Article: main_krylov, s3:def:DC and thm:DC.
Proof: exact real observation reconstruction identifies the retained window
and the true deferred horizon. Its actual determinant transfers to the fixed
array, and the original estimate chart supplies exactly the read branch's domain. -/
theorem deferredDataObserved_actual_regular (memory : ℕ → ℕ) (horizon : ℕ) (estimate : History E → ℝ)
    (H : History E) (r : WithTop ℕ∞)
    (hC : (crossGram (windowImages (selectedWindow memory H)) (windowSteps (selectedWindow memory H))).det≠0)
    (ha : H.records.length+1=horizon →
      ContDiffAt ℝ r (historyEstimateChart estimate H.queryShape H.observationList.length)
        (observedArray H.observationList.length H.observationList))
    (ha0 : H.records.length+1=horizon → estimate H≠0) :
    ContDiffAt ℝ r (deferredDataObservedRule memory horizon estimate H.queryShape H.observationList.length).coefficient
      (observedArray H.observationList.length H.observationList) := by
  let data := observedArray H.observationList.length H.observationList
  let shape := H.queryShape
  have hW : chartWindow memory shape data=selectedWindow memory H := by
    dsimp only [chartWindow,shape,data]
    rw [ofFn_observedArray,historyFromObservations_actual]
  have hlen : (selectedWindow memory H).length=min (memory shape.length) shape.length := by rw [← hW,chartWindow_length]
  have hd : (crossGram (chartImages memory shape data) (chartSteps memory shape data)).det≠0 := by
    change (crossGram (fun i : Fin (min (memory shape.length) shape.length) => ((chartWindow memory shape data).getD i.val (0,0)).2)
      (fun i : Fin (min (memory shape.length) shape.length) => ((chartWindow memory shape data).getD i.val (0,0)).1)).det≠0
    rw [hW,← crossGram_getD_array_det _ _ hlen]
    exact hC
  apply deferredDataObservedRule_coefficient_regular memory horizon estimate shape _ data r hd
  · intro hc
    exact ha (by simpa only [shape,History.queryShape,List.length_map] using hc)
  · intro hc
    rw [historyEstimateChart_actual]
    exact ha0 (by simpa only [shape,History.queryShape,List.length_map] using hc)

end
end krylov.Cancellation
