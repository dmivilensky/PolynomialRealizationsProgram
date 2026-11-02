import krylov.Methods.DataDeferredCoefficients
import krylov.Methods.DeferredObserved
import krylov.Methods.DeferredReindex
import krylov.Cancellation.DCSlide
set_option autoImplicit false
/-!
Article: main_krylov, thm:dcs and s8:dcsdef, actual observed DC-slide coefficient dictionary.
Use: represent genuine data-dependent tilted directions by their original
finite observed-vector coefficients and derive their primitive C-r regularity.
Source: reused actual deferred observed synthesis, genuine finite-list
coordinate invariance and proved variable-estimate native solve calculus.
-/

namespace krylov.Cancellation
noncomputable section
open krylov.Methods krylov.Reference krylov.Stability
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}

/-- The original data-only estimate in its true fixed observed-history chart.
Use: source C-r estimate assumptions concern primitive observed coefficients,
not an assumed smooth estimate along an executed trajectory.
Article: main_krylov, thm:dcs(c) and s8:dcsdef. -/
def historyEstimateChart (estimate : History E → ℝ) (shape : List ℕ) (n : ℕ) : (Fin n → E) → ℝ :=
  fun data => estimate (historyFromObservations shape (List.ofFn data))

/-- The native DC-slide direction compiled into true finite observed coefficients.
Use: the estimate is read from the actual reconstructed observed data before
the chosen physical direction or new operator query is formed.
Article: main_krylov, thm:dcs and s8:dcsdef. -/
def dcObservedRule (memory : ℕ → ℕ) (estimate : History E → ℝ) (shape : List ℕ) (n : ℕ) : ObservedRule E n where
  coefficient data := (deferredObservedRule memory shape n (historyEstimateChart estimate shape n data)).coefficient data

/-- The primitive DC-slide rule evaluates exactly to the original actual
data-dependent tilted direction on its true reconstructed history.
Use: this coefficient dictionary represents the genuine implementation.
Article: main_krylov, thm:dcs and s8:dcsdef.
Proof: reuse the actual deferred observed synthesis at the original observed
estimate, then transfer the true retained array solve to its real list indices. -/
theorem dcObservedRule_evaluate (memory : ℕ → ℕ) (estimate : History E → ℝ)
    (shape : List ℕ) (data : Fin n → E) :
    (dcObservedRule memory estimate shape n).evaluate data=
      dcSlideDirection memory estimate (historyFromObservations shape (List.ofFn data)) := by
  change (deferredObservedRule memory shape n (historyEstimateChart estimate shape n data)).evaluate data=_
  rw [deferredObservedRule_evaluate]
  exact (deferredDirection_getD_array (chartWindow memory shape data) _
    (chartWindow_length memory shape data) (chartGradient shape data)
      (historyEstimateChart estimate shape n data)).symm

/-- Every primitive original DC-slide observed coefficient is C-r under
precisely the true smooth nonzero estimate and actual cross-Gram domain.
Use: no regular trajectory or cancellation response is assumed in the source dictionary.
Article: main_krylov, thm:dcs(c) and lem:U(d).
Proof: actual reconstructed observations have genuine primitive smooth
coordinates. The proved variable-estimate native inverse calculus makes each
true tilted coefficient smooth, and actual fixed observation synthesis preserves it. -/
theorem dcObservedRule_coefficient_regular (memory : ℕ → ℕ) (estimate : History E → ℝ)
    (shape : List ℕ) (data : Fin n → E) (r : WithTop ℕ∞)
    (hC : (crossGram (chartImages memory shape data) (chartSteps memory shape data)).det≠0)
    (ha : ContDiffAt ℝ r (historyEstimateChart estimate shape n) data)
    (ha0 : historyEstimateChart estimate shape n data≠0) :
    ContDiffAt ℝ r (dcObservedRule memory estimate shape n).coefficient data := by
  have hfields := chartSteps_regular memory shape (fun p : Fin n → E => p) data (r := r) contDiffAt_id
  have hgrad := (chartWindow_regular memory shape (fun p : Fin n → E => p) data (r := r) contDiffAt_id).2
  have hc := contDiff_dataDeferredCoefficients (fun p : Fin n → E => chartSteps memory shape p)
    (fun p => chartImages memory shape p) (fun p => chartGradient shape p)
    (historyEstimateChart estimate shape n) data (fun i => (hfields i).1) (fun i => (hfields i).2) hgrad ha ha0 hC
  change ContDiffAt ℝ r (fun p : Fin n → E => -(coefficientHistory shape n).gradient+
    ∑ i : Fin (min (memory shape.length) shape.length),
      deferredCoefficients (chartSteps memory shape p) (chartImages memory shape p) (chartGradient shape p)
        (historyEstimateChart estimate shape n p) i • coefficientStep memory shape n i) data
  exact contDiffAt_const.add (ContDiffAt.sum (fun i _ => (hc i).smul contDiffAt_const))

omit [InnerProductSpace ℝ E] in
/-- The primitive estimate chart reads exactly the estimate on the original
actual complete history, including every genuine observation boundary.
Use: its nonzero domain is the source's actual positive data-only estimate.
Article: main_krylov, thm:dcs and s8:dcsdef.
Proof: true finite observation extraction and reconstruction recover the original history. -/
theorem historyEstimateChart_actual (estimate : History E → ℝ) (H : History E) :
    historyEstimateChart estimate H.queryShape H.observationList.length
      (observedArray H.observationList.length H.observationList)=estimate H := by
  unfold historyEstimateChart
  rw [ofFn_observedArray,historyFromObservations_actual]

/-- Primitive original smooth observed estimates give genuine smooth native
DC coefficients at actual histories with a true nonsingular retained model.
Use: the implemented cycle compiler receives the actual source estimate rule.
Article: main_krylov, thm:dcs(c) and lem:U(d).
Proof: reconstruct the original retained window from actual observations,
transfer its genuine determinant to the true fixed array and apply the proved
primitive data-dependent observed rule calculus at its actual scalar domain. -/
theorem dcObserved_actual_regular (memory : ℕ → ℕ) (estimate : History E → ℝ) (H : History E) (r : WithTop ℕ∞)
    (hC : (crossGram (windowImages (selectedWindow memory H)) (windowSteps (selectedWindow memory H))).det≠0)
    (ha : ContDiffAt ℝ r (historyEstimateChart estimate H.queryShape H.observationList.length)
      (observedArray H.observationList.length H.observationList)) (ha0 : estimate H≠0) :
    ContDiffAt ℝ r (dcObservedRule memory estimate H.queryShape H.observationList.length).coefficient
      (observedArray H.observationList.length H.observationList) := by
  let data := observedArray H.observationList.length H.observationList
  let shape := H.queryShape
  have hW : chartWindow memory shape data=selectedWindow memory H := by
    dsimp only [chartWindow,shape,data]
    rw [ofFn_observedArray,historyFromObservations_actual]
  have hlen : (selectedWindow memory H).length=min (memory shape.length) shape.length := by
    rw [← hW,chartWindow_length]
  have hd : (crossGram (chartImages memory shape data) (chartSteps memory shape data)).det≠0 := by
    change (crossGram (fun i : Fin (min (memory shape.length) shape.length) => ((chartWindow memory shape data).getD i.val (0,0)).2)
      (fun i : Fin (min (memory shape.length) shape.length) => ((chartWindow memory shape data).getD i.val (0,0)).1)).det≠0
    rw [hW,← crossGram_getD_array_det _ _ hlen]
    exact hC
  exact dcObservedRule_coefficient_regular memory estimate shape data r hd ha
    (by rw [historyEstimateChart_actual];exact ha0)

end
end krylov.Cancellation
