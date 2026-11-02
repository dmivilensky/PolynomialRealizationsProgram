import krylov.XR.QuadraticEventRun

/-!
Article: main_krylov, thm:XR, real rejected-probe/accepted-event bridge.
Use: relate the stored-event induction to the literal raw outer executor.
The first rejection is an actual unmoved-anchor event; all later rejected
backtracking evaluations change no stored data. Source: alg:xr control flow.
-/

namespace krylov.XR
noncomputable section
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
local instance quadraticOuterEventDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- Final outer counters use the saved first ModelStep data even when a
rejected probe caused a second ModelStep. -/
def applyOuterCounters (P : Parameters) (dimension : ℕ) (S : State E)
    (firstPairs firstDeleted evaluations : ℕ) (result : State E) : State E :=
  let cap := updateCapacity P dimension S.capacity S.cleanCount firstPairs firstDeleted evaluations
  { result with capacity := cap.1, cleanCount := cap.2 }

/-- Exact raw outer control flow as one accepted stored event, or one
rejected stored probe followed by one accepted event. No acceptance or
trajectory equality is assumed in this executor identity. -/
theorem rawOuterAdvance_event_decomposition (P : Parameters) (dimension : ℕ)
    (model : State E → ModelResult E) (f : E → ℝ) (G : E → E) (S : State E) :
    rawOuterAdvance P dimension model f G S =
      if S.gradient = 0 then S else
        let M₀ := model S
        if Accepted f P.armijo S.point S.gradient M₀.direction 1 then
          applyOuterCounters P dimension S M₀.pairsBeforeTest M₀.deletedByTest 1
            (rawObservationEvent model f G 1 true S)
        else
          let probe := rawObservationEvent model f G 1 false S
          let M₁ := model probe
          let j := backtrackingIndex f P.armijo S.point S.gradient M₁.direction
          applyOuterCounters P dimension S M₀.pairsBeforeTest M₀.deletedByTest (j + 2)
            (rawObservationEvent model f G
              (backtrackingSteps f S.point S.gradient M₁.direction j) true probe) := by
  classical
  unfold rawOuterAdvance
  split
  · rfl
  · unfold rawOuterSearch
    dsimp only
    split
    · unfold rawObservationEvent applyOuterCounters
      simp only [one_smul]
      rfl
    · unfold rawObservationEvent applyOuterCounters
      simp only [one_smul]
      rfl

end
end krylov.XR
