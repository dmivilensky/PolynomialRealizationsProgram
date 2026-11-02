import krylov.Stability.LaggedRegularity
import krylov.Stability.TrialCoordinates
set_option autoImplicit false
/-!
Article: main_krylov, prop:hb, primitive observed-coordinate lagged smoothness.
Use: the exact trial-coordinate hypothesis of the native XRFC Taylor theorems
is derived for the real implemented lagged rule, at its algebraic replay domain.
Source: the actual chronological replay regularity and the genuine history chart.
-/

namespace krylov.Stability
noncomputable section
open krylov.Methods
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The genuine primitive observed-coordinate lagged trial is C^r at every
positive nonsingular replay history.
Use: supplies exactly the original native Taylor theorem's primitive trial
hypothesis, with no assumed trajectory or trial regularity.
Article: main_krylov, prop:hb.
Proof: the true finite history chart has smooth coordinate projections for
each actual step and returned gradient. Apply the proved full cache induction. -/
theorem contDiff_laggedTrialCoordinate {r : WithTop ℕ∞} (directions : Bool)
    (tau0 : ℝ) (k : ℕ) (data : E × (Fin k → E) × (Fin k → E))
    (hdomain : laggedReplayDomain directions tau0 data.1 (oneGradientHistoryChart data).records) :
    ContDiffAt ℝ r (trialCoordinate (laggedTrial directions tau0) k) data := by
  let D := E × (Fin k → E) × (Fin k → E)
  let records : List (D → IterationRecord E) :=
    List.ofFn (fun i : Fin k => fun z => ⟨0,0,z.2.1 i,z.2.2 i,[]⟩)
  have hrecords (z : D) : records.map (fun f => f z)=(oneGradientHistoryChart z).records := by
    rw [List.map_ofFn]
    rfl
  have hs (f : D → IterationRecord E) (hf : f∈records) :
      ContDiffAt ℝ r (fun z => (f z).step) data := by
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hf
    exact contDiffAt_pi.mp (contDiffAt_fst.comp data contDiffAt_snd) i
  have hg (f : D → IterationRecord E) (hf : f∈records) :
      ContDiffAt ℝ r (fun z => (f z).gradient) data := by
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hf
    exact contDiffAt_pi.mp (contDiffAt_snd.comp data contDiffAt_snd) i
  have hd : laggedReplayDomain directions tau0 data.1 (records.map (fun f => f data)) := by
    rw [hrecords]
    exact hdomain
  have h := (contDiff_laggedReplay directions tau0 (fun z : D => z.1) records data
    contDiffAt_fst hs hg hd).2
  apply h.congr_of_eventuallyEq
  apply Filter.Eventually.of_forall
  intro z
  change (laggedReplay directions tau0 z.1 (oneGradientHistoryChart z).records).2=_
  exact congrArg (fun rs => (laggedReplay directions tau0 z.1 rs).2) (hrecords z).symm

end
end krylov.Stability
