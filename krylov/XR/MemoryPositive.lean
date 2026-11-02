import krylov.XR.MemoryObservations

/-!
Article: main_krylov, alg:xr and G2, genuine retained nonzero steps.
Use: prove that every stored observation passes its actual positive-curvature
test and hence has a nonzero physical step. This is an invariant of the
literal executor, independently of the source function and acceptance.
Source: appendPositive, suffix retention and exact anchor transport.
-/

namespace krylov.XR
noncomputable section
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The append guard itself ensures positivity of every retained pair. -/
theorem appendPositive_positive (W : List (PairObservation E)) (P : PairObservation E)
    (hW : ∀ a ∈ W, positivePair a) : ∀ a ∈ appendPositive W P, positivePair a := by
  classical
  unfold appendPositive
  split
  · rename_i hp
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact hW a ha
    · simpa only [List.mem_singleton.mp ha] using hp
  · exact hW

/-- Anchor transport changes no observed curvature. -/
theorem positivePair_transport (P : PairObservation E) (s : E) :
    positivePair (P.transport s) ↔ positivePair P := Iff.rfl

/-- Every true positive-curvature stored observation has nonzero step. -/
theorem positivePair_step_ne_zero (P : PairObservation E) (hP : positivePair P) : P.step ≠ 0 := by
  intro hz
  unfold positivePair at hP
  rw [hz, inner_zero_left] at hP
  exact hP.false

/-- The actual one-rejected-probe search preserves positive stored data. -/
theorem outerSearch_positive (model : State E → ModelResult E)
    (hmodel : ∀ S : State E, (∀ a ∈ S.pairs, positivePair a) →
      ∀ a ∈ (model S).pairs, positivePair a)
    (f : E → ℝ) (G : E → E) (sigma : ℝ) (S : State E)
    (hS : ∀ a ∈ S.pairs, positivePair a) :
    ∀ a ∈ (outerSearch model f G sigma S).pairs, positivePair a := by
  classical
  unfold outerSearch
  dsimp only
  split
  · exact hmodel S hS
  · apply hmodel
    exact appendPositive_positive _ _ (hmodel S hS)

/-- Positive observations remain positive after every actual accepted
update, including its transported rejected probe. -/
theorem outerAdvance_positive (P : Parameters) (dimension : ℕ)
    (model : State E → ModelResult E)
    (hmodel : ∀ S : State E, (∀ a ∈ S.pairs, positivePair a) →
      ∀ a ∈ (model S).pairs, positivePair a)
    (f : E → ℝ) (G : E → E) (S : State E) (hS : ∀ a ∈ S.pairs, positivePair a) :
    ∀ a ∈ (outerAdvance P dimension model f G S).pairs, positivePair a := by
  classical
  unfold outerAdvance
  split
  · exact hS
  · dsimp only
    intro a ha
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    exact (positivePair_transport b _).2
      (appendPositive_positive _ _ (outerSearch_positive model hmodel f G P.armijo S hS) b hb)

/-- The complete literal algorithm stores only actual positive-curvature
observations. In particular normalization of every real window is defined. -/
theorem algorithmRun_pairs_positive {n : ℕ} (P : Parameters)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (x₀ : EuclideanSpace ℝ (Fin n)) (bounds : SpectralBounds) (k : ℕ) :
    ∀ a ∈ (algorithmRun P f G x₀ bounds k).pairs, positivePair a := by
  induction k with
  | zero => simp [algorithmRun, run, algorithmInitialState, initialState]
  | succ k ih =>
    apply outerAdvance_positive P n (algorithmModel P) _ f G _ ih
    intro S hS a ha
    exact hS a (algorithmModel_pair_mem P S a ha)

end
end krylov.XR
