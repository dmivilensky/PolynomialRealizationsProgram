import krylov.Cancellation.DCSchurNative
import krylov.Cancellation.DeferredDataSmooth
set_option autoImplicit false
/-!
Article: main_krylov, thm:DC, genuine smooth interval-rule continuation.
Use: the actual deferred arithmetic Gauss--Radau implementation has its
original reference values and primitive charts, including band endpoints.
Source: exact deferred/DC/FC quadratic history dictionaries, proper active
Krylov pencils and the original observed rational Schur continuation.
-/

namespace krylov.Cancellation
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Stability krylov.Completion
open scoped InnerProductSpace
variable {n : ℕ}

/-- The actual deferred arithmetic Schur estimate is positive, has its
primitive observed chart of every order and equals the original interval
rule on its genuine quadratic reference, including physical band endpoints.
Use: no smooth estimate, strict physical spectral interior or hypothetical
reference history is supplied to deferred cancellation's source theorems.
Article: main_krylov, thm:DC, true deferred interval continuation dictionary.
Proof: both complete native quadratic histories equal the same FC history.
The actual sliding history supplies independent proper-Krylov columns,
true images and positive descent. Reuse the proved native Schur chart and
physical endpoint dictionaries, then transfer all three exact conclusions
along the true equality of complete histories. -/
theorem deferred_schur_reference_data (memory : ℕ → ℕ) (hm : ∀ k,0<k → 0<memory k)
    (horizon : ℕ) (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (mu upper : ℝ) (hmu : 0<mu) (hmuL : mu≤upper)
    (hlo : (base-mu • 1).PosSemidef) (hhi : (upper • 1-base).PosSemidef)
    (g : EuclideanSpace ℝ (Fin n)) (k : ℕ)
    (hpre : ∀ i<k+1,CG.gradient (cgOperator base) g i≠0) (r : WithTop ℕ∞) :
    let estimate := dcSchurGaussRadauEstimate memory mu upper (n := n)
    let H := methodRun (deferredDataMethod memory horizon estimate)
      (fun _ => cgOperator base) (fun _ => cgOperator base) g k
    0<estimate H ∧
      ContDiffAt ℝ r (historyEstimateChart estimate H.queryShape H.observationList.length)
        (observedArray H.observationList.length H.observationList) ∧
      dcGaussRadauEstimate memory mu upper H=estimate H := by
  let Q := cgOperator base
  let estimate := dcSchurGaussRadauEstimate memory mu upper (n := n)
  let H := methodRun (deferredDataMethod memory horizon estimate) (fun _ => Q) (fun _ => Q) g k
  let J := methodRun (dcSlideMethod memory estimate) (fun _ => Q) (fun _ => Q) g k
  have hp := cgOperator_positive base hb
  have hHJ : H=J := (deferred_data_reference_run memory hm horizon estimate Q hp.1 hp.2 g k).trans
    (dc_slide_reference_run memory hm estimate Q hp.1 hp.2 g k).symm
  have hi := dc_reference_inputs memory hm estimate Q hp.1 hp.2 g k hpre
  have hdata : 0<estimate J ∧ ContDiffAt ℝ r (historyEstimateChart estimate
      J.queryShape J.observationList.length) (observedArray J.observationList.length J.observationList) :=
    dc_schur_reference_estimate memory J base hb g k hpre mu upper hmu hmuL hlo hhi
      hi.2.1 hi.1 hi.2.2.1 hi.2.2.2 r
  have hform := physical_band_operator_forms base mu upper hlo hhi
  have hproper := proper_observed_window_pencils (selectedWindow memory J) base hb g k hpre mu upper
    hform.1 hform.2 hi.2.1 hi.1 hi.2.2.1
  have hphys := dc_quadratic_window_feasible memory J base hb mu upper hlo hhi hi.2.1 hi.1 hi.2.2.2
  have heq := dc_schur_estimate_original memory mu upper J hmu hmuL hphys.1 hphys.2.1
    hproper.1 hproper.2 (Set.nonempty_of_mem hphys.2.2)
  change 0<estimate H ∧
    ContDiffAt ℝ r (historyEstimateChart estimate H.queryShape H.observationList.length)
      (observedArray H.observationList.length H.observationList) ∧
    dcGaussRadauEstimate memory mu upper H=estimate H
  rw [hHJ]
  exact ⟨hdata.1,hdata.2,heq⟩

/-- The literal deferred arithmetic Schur implementation has genuine
native smooth-cycle membership of every order on its entire active
physical-band reference, including endpoint spectra and collapsed rules.
Use: all actual deferred derivative and compact Taylor theorems have
their original estimate hypotheses discharged for this concrete policy.
Article: main_krylov, thm:DC, actual smooth interval deferred executor.
Proof: apply the existing exact native observed-rule compiler. The actual
reference dictionary supplies its positive scalar and smooth chart only
on the final branch where the genuine deferred executor reads the estimate. -/
theorem deferred_schur_smoothCycleAt (memory : ℕ → ℕ) (hm : ∀ k,0<k → 0<memory k)
    (horizon : ℕ) (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (mu upper : ℝ) (hmu : 0<mu) (hmuL : mu≤upper)
    (hlo : (base-mu • 1).PosSemidef) (hhi : (upper • 1-base).PosSemidef)
    (g : EuclideanSpace ℝ (Fin n)) (N : ℕ)
    (hpre : ∀ i<N,CG.gradient (cgOperator base) g i≠0) (r : WithTop ℕ∞) :
    SmoothProbedCycleAt (deferredDataMethod memory horizon
      (dcSchurGaussRadauEstimate memory mu upper)) r (cgOperator base) g N := by
  have hp := cgOperator_positive base hb
  apply deferred_data_smoothCycleAt memory hm horizon _ _ hp.1 hp.2 g N hpre r
  · intro k hk _
    exact (deferred_schur_reference_data memory hm horizon base hb mu upper hmu hmuL hlo hhi g k
      (fun i hi => hpre i (by omega)) r).2.1
  · intro k hk _
    exact (deferred_schur_reference_data memory hm horizon base hb mu upper hmu hmuL hlo hhi g k
      (fun i hi => hpre i (by omega)) r).1

end
end krylov.Cancellation
