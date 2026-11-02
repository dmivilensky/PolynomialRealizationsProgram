import krylov.XR.LocalFullWindow
import krylov.XR.MemoryPositive
import krylov.XR.MemoryRank

/-!
Article: main_krylov, thm:grow, genuine incoming-window branch activation.
Use: apply G2 before rank cleanup, deriving that neither the actual rank
test nor the actual Hermitian test deletes a pair. The source assumptions
are physical relative secant errors and normalized independence; no desired
retention or branch decision is a field. Source: primitive raw-window bounds.
-/

namespace krylov.XR
noncomputable section
open Matrix Set krylov.Methods krylov.Secant
open scoped InnerProductSpace
variable {n : ℕ}

/-- Literal pre-cleanup window appearing in the intended G2 hypothesis. -/
def incomingWindow (S : State (EuclideanSpace ℝ (Fin n))) :
    List (PairObservation (EuclideanSpace ℝ (Fin n))) := retainNewest (min S.capacity n) S.pairs

/-- Incoming windows consist of genuinely stored nonzero steps. -/
theorem incomingWindow_steps_ne_zero (S : State (EuclideanSpace ℝ (Fin n)))
    (hS : ∀ a ∈ S.pairs, positivePair a) (i : Fin (incomingWindow S).length) :
    storedSteps (incomingWindow S) i ≠ 0 := by
  apply positivePair_step_ne_zero
  exact hS _ (List.mem_of_mem_drop (List.get_mem _ i))

/-- Actual rank and refutation cleanup retain the entire incoming window
on primitive sufficiently accurate/independent physical secants. -/
theorem algorithmModel_local_retention (P : Parameters) (htheta : 0 < P.windowThreshold)
    (S : State (EuclideanSpace ℝ (Fin n))) (hS : ∀ a ∈ S.pairs, positivePair a)
    (H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hH : H.toLinearMap.IsSymmetric) (mu sigma epsilon : ℝ)
    (hmu : 0 < mu) (hsigma : 0 < sigma) (he : 0 ≤ epsilon)
    (hpositive : ∀ v, mu * ‖v‖ ^ 2 ≤ inner ℝ v (H v))
    (hgain : ∀ w : Fin (incomingWindow S).length → ℝ,
      sigma ^ 2 * ‖WithLp.toLp 2 w‖ ^ 2 ≤
        ‖combine (krylov.Convergence.unitWindow (storedSteps (incomingWindow S))) w‖ ^ 2)
    (hy : ∀ i, ‖storedImages (incomingWindow S) i - H (storedSteps (incomingWindow S) i)‖ ≤
      epsilon * ‖storedSteps (incomingWindow S) i‖)
    (hsmall : ((incomingWindow S).length : ℝ) * epsilon ≤ mu * sigma ^ 2 / 4)
    (hgate : 2 * ((incomingWindow S).length : ℝ) * epsilon / localCoercivity mu sigma < P.windowThreshold) :
    rankDeletion (incomingWindow S) = 0 ∧
      (algorithmModel P S).pairs = incomingWindow S ∧
      (algorithmModel P S).pairsBeforeTest = (incomingWindow S).length ∧
      (algorithmModel P S).deletedByTest = 0 := by
  have hs := incomingWindow_steps_ne_zero S hS
  have hdom := local_raw_window_domains H hH (storedSteps (incomingWindow S)) (storedImages (incomingWindow S))
    hs mu sigma epsilon hmu hsigma he hpositive hgain hy hsmall
  have hrank := rankDeletion_eq_zero (incomingWindow S) hdom.1
  have hrankWindow : rankWindow n S = incomingWindow S := by
    change (incomingWindow S).drop (rankDeletion (incomingWindow S)) = incomingWindow S
    rw [hrank, List.drop_zero]
  have hpass : windowUnrefuted P.windowThreshold (storedPairing (incomingWindow S)) :=
    local_raw_windowUnrefuted P.windowThreshold htheta H hH
      (storedSteps (incomingWindow S)) (storedImages (incomingWindow S)) hs mu sigma epsilon
      hmu hsigma he hpositive hgain hy hsmall hgate
  have hdelete := modelDeletion_eq_zero P (incomingWindow S) hpass
  exact ⟨hrank, by simp only [algorithmModel, hrankWindow, hdelete, List.drop_zero],
    by simp only [algorithmModel, hrankWindow], by simp only [algorithmModel, hrankWindow, hdelete]⟩

end
end krylov.XR
