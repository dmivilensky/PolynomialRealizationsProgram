import krylov.Cancellation.DCNativeSmooth
import krylov.Methods.SmoothProbedFields
set_option autoImplicit false
/-!
Article: main_krylov, thm:dcs(c), actual observed estimate regularity.
Use: derive smoothness of the chosen original scalar on genuine executed
histories from its primitive fixed-shape observed-data coefficient chart.
Source: actual full-history smooth observation charts, exact history
reconstruction and standard finite C-r composition.
-/

namespace krylov.Cancellation
noncomputable section
open Filter Topology krylov.Methods krylov.Reference krylov.Stability
variable {E X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- A scalar observed-history rule inherits C-r regularity on an actual
smooth full history with its genuine locally fixed query boundaries.
Use: the cancellation estimate is derived from primitive observed coordinates,
not assumed smooth along a desired trajectory.
Article: main_krylov, thm:dcs(c).
Proof: the genuine finite observation chart fixes its true coordinate count;
compose the primitive scalar rule and reconstruct the exact original history
on its real fixed-shape execution neighborhood. -/
theorem actual_history_estimate_contDiffAt {r : WithTop ℕ∞}
    (estimate : History E → ℝ) (H : X → History E) (x : X)
    (htrace : SmoothListAt r (fun p => (H p).observationList) x)
    (hshape : ∀ᶠ p in 𝓝 x,(H p).queryShape=(H x).queryShape)
    (ha : ContDiffAt ℝ r (historyEstimateChart estimate (H x).queryShape (H x).observationList.length)
      (observedArray (H x).observationList.length (H x).observationList)) :
    ContDiffAt ℝ r (fun p => estimate (H p)) x := by
  obtain ⟨n,data,hd,he⟩ := htrace
  have he0 : (H x).observationList=List.ofFn (data x) := he.self_of_nhds
  have hchart : ContDiffAt ℝ r (historyEstimateChart estimate (H x).queryShape n) (data x) := by
    rw [he0,List.length_ofFn,observedArray_ofFn] at ha
    exact ha
  apply (hchart.comp x hd).congr_of_eventuallyEq
  filter_upwards [he,hshape] with p hp hs
  change estimate (H p)=estimate (historyFromObservations (H x).queryShape (List.ofFn (data p)))
  rw [← hp,← hs,historyFromObservations_actual]

/-- The actual DC estimate selected from its true exact-search observed
history is C-r under the original primitive smooth estimate hypotheses.
Use: freeze reference estimate values only after their true executed
regularity has been proved from original data-only rules.
Article: main_krylov, thm:dcs(c).
Proof: primitive DC compilation and genuine CG consistency give the actual
full smooth observation trace. Every original correction is empty, so the
true query shape is independent of the perturbed data. Compose the real
primitive scalar coefficient chart with that actual trace. -/
theorem dc_slide_estimate_contDiffAt (memory : ℕ → ℕ) (hm : ∀ k,0<k → 0<memory k)
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
    (ha0 : ∀ k<N,0<estimate (methodRun (dcSlideMethod memory estimate) (fun _ => Q) (fun _ => Q) (g x) k))
    (k : ℕ) (hk : k<N) :
    ContDiffAt ℝ r (fun p => estimate (methodRun (dcSlideMethod memory estimate) (A p) (B p) (g p) k)) x := by
  let m := dcSlideMethod memory estimate
  have hsmooth := dc_slide_smoothCycleAt memory hm estimate Q hQ hpos (g x) N hpre r ha ha0
  have ht := smoothProbed_trace_regular m (dc_slide_consistent memory hm estimate) A B g x k
    (fun i hi => hA i (hi.trans hk)) (fun i hi => hB i (hi.trans hk)) hg Q hAx hBx hQ hpos
    (fun i hi => hpre i (hi.trans hk)) (hsmooth.mono m hk.le)
  apply actual_history_estimate_contDiffAt estimate _ x ht
  · exact Eventually.of_forall fun p =>
      (methodRun_empty_corrections_shape m (fun _ _ => rfl) (A p) (B p) (g p) k).trans
        (methodRun_empty_corrections_shape m (fun _ _ => rfl) (A x) (B x) (g x) k).symm
  · have heq : methodRun m (A x) (B x) (g x) k=methodRun (dcSlideMethod memory estimate) (fun _ => Q) (fun _ => Q) (g x) k := by
      rw [hAx,hBx]
    rw [heq]
    exact ha k hk

end
end krylov.Cancellation
