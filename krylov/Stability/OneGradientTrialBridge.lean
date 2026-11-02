import krylov.Cancellation.DCEstimateRegularity
import krylov.Stability.TrialCoordinates
set_option autoImplicit false
/-!
Article: main_krylov, lem:U(d), actual one-gradient/full-history chart bridge.
Use: transfer proved smooth primitive full observed-history scalar rules to
the original one-gradient trial coordinates, without an assumed trajectory.
Source: genuine finite observed lists, the actual one-gradient history chart
and exact full-history reconstruction/estimate composition.
-/

namespace krylov.Stability
noncomputable section
open Filter Topology krylov.Methods krylov.Cancellation
variable {E X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Concatenating a fixed finite family of actual smooth observed blocks
gives one genuine finite smooth list chart.
Use: the original complete one-gradient observation transcript retains all
real block coordinates, including its zero direction/probe slots.
Article: main_krylov, lem:U(d).
Proof: induct through the finite blocks and reuse true smooth list append. -/
theorem smoothList_ofFn_flatten {k : ℕ} {r : WithTop ℕ∞}
    (blocks : Fin k → X → List E) (x : X) (hblocks : ∀ i,SmoothListAt r (blocks i) x) :
    SmoothListAt r (fun z => (List.ofFn (fun i => blocks i z)).flatten) x := by
  induction k with
  | zero => exact SmoothListAt.nil r x
  | succ k ih =>
    have htail := ih (fun i => blocks i.succ) (fun i => hblocks i.succ)
    convert! (hblocks 0).append htail using 1
    funext z
    rw [List.ofFn_succ,List.flatten_cons]

omit [NormedAddCommGroup X] [NormedSpace ℝ X] in
/-- The genuine full observation list of the primitive one-gradient chart
is C-r in that actual finite initial/step/returned-gradient coordinate tuple.
Use: bridge complete-history scalar regularity to native one-gradient trials.
Article: main_krylov, lem:U(d).
Proof: all real record blocks have four smooth coordinate projections; their
true finite concatenation and both leading current/initial observations are smooth. -/
theorem oneGradient_chart_observations_regular {k : ℕ} (r : WithTop ℕ∞)
    (data : E × (Fin k → E) × (Fin k → E)) :
    SmoothListAt r (fun z => (oneGradientHistoryChart z).observationList) data := by
  let D := E × (Fin k → E) × (Fin k → E)
  let blocks := fun i : Fin k => fun z : D => [0,0,z.2.1 i,z.2.2 i]
  have hblocks (i : Fin k) : SmoothListAt r (blocks i) data := by
    apply SmoothListAt.cons contDiffAt_const
    apply SmoothListAt.cons contDiffAt_const
    apply SmoothListAt.cons (contDiffAt_pi.mp (contDiffAt_fst.comp data contDiffAt_snd) i)
    exact SmoothListAt.cons (contDiffAt_pi.mp (contDiffAt_snd.comp data contDiffAt_snd) i)
      (SmoothListAt.nil r data)
  have hrecord := smoothList_ofFn_flatten blocks data hblocks
  have hcurrent : ContDiffAt ℝ r (fun z : D => (oneGradientHistoryChart z).gradient) data := by
    cases k with
    | zero => exact contDiffAt_fst
    | succ k =>
      have hcoord : ContDiffAt ℝ r (fun z : E × (Fin (k+1) → E) × (Fin (k+1) → E) => z.2.2 0) data :=
        contDiffAt_pi.mp (contDiffAt_snd.comp data contDiffAt_snd) 0
      apply hcoord.congr_of_eventuallyEq
      apply Eventually.of_forall
      intro z
      change (oneGradientHistoryChart z).gradient=z.2.2 0
      rw [oneGradientHistoryChart,List.ofFn_succ]
      rfl
  have hfull := SmoothListAt.cons hcurrent (SmoothListAt.cons contDiffAt_fst hrecord)
  convert! hfull using 1
  funext z
  simp [History.observationList,oneGradientHistoryChart,List.flatMap,blocks,Function.comp_def]

omit [NormedAddCommGroup X] [NormedSpace ℝ X] [InnerProductSpace ℝ E] in
/-- Every primitive one-gradient history has its actual fixed empty-correction
query shape, independent of all real observed coordinate values.
Use: the complete-history chart bridge keeps genuine query boundaries fixed.
Article: main_krylov, lem:U(d).
Proof: each actual primitive record has an empty correction list. -/
theorem oneGradient_chart_queryShape {k : ℕ} (data : E × (Fin k → E) × (Fin k → E)) :
    (oneGradientHistoryChart data).queryShape=List.replicate k 0 := by
  simp [History.queryShape,oneGradientHistoryChart,Function.comp_def]

omit [NormedAddCommGroup X] [NormedSpace ℝ X] in
/-- Genuine primitive complete-history estimate smoothness implies exactly
the original native one-gradient trial-coordinate smoothness.
Use: the source estimate rule can be proved once in full observed coordinates
and then used by either native information protocol without a regularity gap.
Article: main_krylov, lem:U(d) and s8:dcsdef.
Proof: the real primitive one-gradient transcript has a proved smooth full
observation list and fixed actual query shape. Compose its proved full-history
estimate chart using the existing exact actual-history estimate theorem. -/
theorem trialCoordinate_of_history_estimate {k : ℕ} {r : WithTop ℕ∞}
    (estimate : History E → ℝ) (data : E × (Fin k → E) × (Fin k → E))
    (hestimate :
      let H := oneGradientHistoryChart data
      ContDiffAt ℝ r (historyEstimateChart estimate H.queryShape H.observationList.length)
        (observedArray H.observationList.length H.observationList)) :
    ContDiffAt ℝ r (trialCoordinate estimate k) data := by
  apply actual_history_estimate_contDiffAt estimate (fun z => oneGradientHistoryChart z) data
    (oneGradient_chart_observations_regular r data) _ hestimate
  exact Eventually.of_forall (fun z => (oneGradient_chart_queryShape z).trans (oneGradient_chart_queryShape data).symm)

end
end krylov.Stability
