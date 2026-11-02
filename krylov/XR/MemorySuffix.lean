import krylov.XR.MemoryGoodSuffix
import krylov.XR.MemoryRank

/-!
Article: main_krylov, proof of thm:grow, literal chronological retention.
Use: show that the concrete algorithm always deletes an actual oldest
prefix and that its post-update memory has at most n+1 observations.
Source: the three displayed suffix operations and the genuine append guard.
-/

namespace krylov.XR
noncomputable section
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The number of original chronological entries deleted by ModelStep. -/
def modelDropCount {n : ℕ} (P : Parameters) (S : State (EuclideanSpace ℝ (Fin n))) : ℕ :=
  (S.pairs.length - min S.capacity n) +
    rankDeletion (retainNewest (min S.capacity n) S.pairs) + modelDeletion P (rankWindow n S)

/-- Actual model retention is precisely an oldest-prefix deletion, not
an arbitrary subsequence or an assumed provenance relation. -/
theorem algorithmModel_pairs_drop {n : ℕ} (P : Parameters)
    (S : State (EuclideanSpace ℝ (Fin n))) :
    (algorithmModel P S).pairs = S.pairs.drop (modelDropCount P S) := by
  change ((S.pairs.drop (S.pairs.length - min S.capacity n)).drop
    (rankDeletion (retainNewest (min S.capacity n) S.pairs))).drop
      (modelDeletion P (rankWindow n S)) = _
  simp only [List.drop_drop, modelDropCount, Nat.add_assoc]

/-- At most one real observation is appended by the actual curvature guard. -/
theorem appendPositive_length_le (W : List (PairObservation E)) (P : PairObservation E) :
    (appendPositive W P).length ≤ W.length + 1 := by
  classical
  unfold appendPositive
  split
  · simp only [List.length_append, List.length_singleton, le_refl]
  · omega

/-- The single rejected-probe reset still returns a model-sized window. -/
theorem outerSearch_pairs_length_le (model : State E → ModelResult E) (bound : ℕ)
    (hmodel : ∀ S, (model S).pairs.length ≤ bound)
    (f : E → ℝ) (G : E → E) (sigma : ℝ) (S : State E) :
    (outerSearch model f G sigma S).pairs.length ≤ bound := by
  classical
  unfold outerSearch
  dsimp only
  split <;> apply hmodel

/-- Actual accepted updates retain at most n+1 real entries. -/
theorem outerAdvance_pairs_length_le (P : Parameters) (dimension : ℕ)
    (model : State E → ModelResult E) (bound : ℕ)
    (hmodel : ∀ S, (model S).pairs.length ≤ bound)
    (f : E → ℝ) (G : E → E) (S : State E) (hS : S.pairs.length ≤ bound + 1) :
    (outerAdvance P dimension model f G S).pairs.length ≤ bound + 1 := by
  classical
  unfold outerAdvance
  split
  · exact hS
  · dsimp only
    rw [List.length_map]
    exact (appendPositive_length_le _ _).trans (Nat.add_le_add_right
      (outerSearch_pairs_length_le model bound hmodel f G P.armijo S) 1)

/-- Complete literal XR has the post-update memory bound needed by the
finite-forgetting argument, even in the rejected-probe branch. -/
theorem algorithmRun_pairs_length_le {n : ℕ} (P : Parameters)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (x₀ : EuclideanSpace ℝ (Fin n)) (bounds : SpectralBounds) (k : ℕ) :
    (algorithmRun P f G x₀ bounds k).pairs.length ≤ n + 1 := by
  induction k with
  | zero => simp [algorithmRun, run, algorithmInitialState, initialState]
  | succ k ih =>
    exact outerAdvance_pairs_length_le P n (algorithmModel P) n
      (fun S => (algorithmModel_length_le P S).trans (min_le_right _ _)) f G _ ih

/-- Physical proximity of both genuine endpoints of a stored observation. -/
def PairNear (center : E) (radius : ℝ) (P : PairObservation E) : Prop :=
  ‖P.anchor - center‖ < radius ∧ ‖P.anchor + P.step - center‖ < radius

/-- Anchor-pairing transport does not change the genuine segment endpoints. -/
theorem pairNear_transport (center : E) (radius : ℝ) (P : PairObservation E) (s : E) :
    PairNear center radius (P.transport s) ↔ PairNear center radius P := Iff.rfl

end
end krylov.XR
