import krylov.Cancellation.DCConsistentCycle
import krylov.Cancellation.DeferredDataTaylor
set_option autoImplicit false
/-!
Article: main_krylov, apH:dcs2(b), actual sliding/deferred end-cycle comparison.
Use: compare the two original native terminal gradients with a genuine
quadratic remainder under only C-one consistent sliding estimates.
Source: proved full native C-one sliding expansion and the original actual
constant-calibrated deferred C-two expansion, both on the same physical source.
-/

namespace krylov.Cancellation
noncomputable section
open Matrix Filter Asymptotics krylov.Methods krylov.Reference krylov.Secant krylov.Stability krylov.Variation
open scoped Topology Matrix.Norms.L2Operator
variable {n : ℕ}

/-- Consistent full-memory exact-search DC-slide and the actual calibrated
deferred method have terminal canonical gradients differing by quadratic
order on every original symmetric source axis.
Use: compares the real returned gradients of both implementations, after
accounting for all actual moving step bases, without a response-equality premise.
Article: main_krylov, apH:dcs2(b), original end-cycle comparison.
Proof: both genuine full canonical outputs equal the same proved calibrated
fresh response with true quadratic remainders. Native sliding reconstruction
requires only the original C-one estimate charts. The calibrated deferred
estimate is constant and therefore C-two; its genuine reference line length
is positive. Subtract the two actual remainders. -/
theorem dc_slide_deferred_end_cycle_order
    (estimate : History (EuclideanSpace ℝ (Fin n)) → ℝ)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (k : ℕ)
    (hcount : referenceAtomCount base hb g=n) (hfull : k+1=n)
    (ha : ∀ j<k+1,
      let H := methodRun (dcSlideMethod fullMemory estimate) (fun _ => cgOperator base) (fun _ => cgOperator base) g j
      ContDiffAt ℝ 1 (historyEstimateChart estimate H.queryShape H.observationList.length)
        (observedArray H.observationList.length H.observationList))
    (ha0 : ∀ j<k+1,0<estimate (methodRun (dcSlideMethod fullMemory estimate)
      (fun _ => cgOperator base) (fun _ => cgOperator base) g j))
    (hcal : ∀ j<k+1,estimate (methodRun (dcSlideMethod fullMemory estimate)
      (fun _ => cgOperator base) (fun _ => cgOperator base) g j)=CG.length (cgOperator base) g j)
    (E : ℕ → Matrix (Fin n) (Fin n) ℝ) (hE : ∀ l,(E l).IsSymm) :
    let A := canonicalFCPath base E
    let a := CG.length (cgOperator base) g k
    let m := dcSlideMethod fullMemory estimate
    let d : ProbedMethod (EuclideanSpace ℝ (Fin n)) := deferredDataMethod fullMemory (k+1) (fun _ => a)
    (fun t : ℝ => cgOperator (metricRoot base)⁻¹
      (probedGradient m (A t) (A t) g (k+1)-probedGradient d (A t) (A t) g (k+1)))
        =O[𝓝 (0 : ℝ)] (fun t => ‖t‖^2) := by
  let A := canonicalFCPath base E
  let a := CG.length (cgOperator base) g k
  let m := dcSlideMethod fullMemory estimate
  let d : ProbedMethod (EuclideanSpace ℝ (Fin n)) := deferredDataMethod fullMemory (k+1) (fun _ => a)
  let R := cgOperator (metricRoot base)⁻¹
  let L := deferredResponse base g k 0 E
  have hpos : 0<a := cgLength_pos base hb g k (by omega)
  have hM := dc_slide_consistent_canonical_order estimate base hb g k hcount hfull E hE A
    (fun j _ => (canonicalFCPath_calculus base E j).1.contDiffAt) (canonicalFCPath_zero base E) ha ha0 hcal
  have hchart :
      let H := methodRun d (fun _ => cgOperator base) (fun _ => cgOperator base) g k
      ContDiffAt ℝ 2 (historyEstimateChart (fun _ => a) H.queryShape H.observationList.length)
        (observedArray H.observationList.length H.observationList) := contDiffAt_const
  obtain ⟨delta,C,hd,_,hbound⟩ := deferred_data_canonical_expansion (fun _ => a) base hb g E hE A k
    (fun j _ => (canonicalFCPath_calculus base E j).1.contDiffAt) (canonicalFCPath_zero base E)
    hcount hfull hchart hpos
  have hD : (fun t : ℝ => R (probedGradient d (A t) (A t) g (k+1))-t • L)
      =O[𝓝 (0 : ℝ)] (fun t => ‖t‖^2) := by
    refine IsBigO.of_bound C ?_
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hd] with t ht
    have ht' : |t|<delta := by simpa only [Metric.mem_ball,dist_zero_right,Real.norm_eq_abs] using ht
    have hh := hbound t ht'.le
    change ‖R (probedGradient d (A t) (A t) g (k+1))-
      t • deferredResponse base g k (1-a/a) E‖≤C*t^2 at hh
    rw [div_self hpos.ne',sub_self] at hh
    simpa only [norm_pow,norm_norm,Real.norm_eq_abs,sq_abs] using hh
  apply (hM.sub hD).congr_left
  intro t
  change (R (probedGradient m (A t) (A t) g (k+1))-t • L)-
    (R (probedGradient d (A t) (A t) g (k+1))-t • L)=_
  rw [map_sub]
  abel

end
end krylov.Cancellation
