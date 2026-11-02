import krylov.XR.AlgorithmModel
import krylov.XR.Global

/-!
Article: main_krylov, alg:xr and cor:xrF, genuine cached window observations.
Use: prove the data retained by the literal ModelStep are real secants and
endpoint defects, and that anchor transport is an exact invariant.
Source: actual scalar/gradient evaluations and elementary pairing algebra.
-/

namespace krylov.XR
noncomputable section
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Exact meaning of a stored observation at the current accepted point. -/
def PairFaithful (f : E → ℝ) (G : E → E) (x : E) (P : PairObservation E) : Prop :=
  P.image = G (P.anchor + P.step) - G P.anchor ∧
    P.valueDefect = f (P.anchor + P.step) - f P.anchor -
      inner ℝ (G P.anchor) P.step - inner ℝ P.step P.image / 2 ∧
    P.anchorPairing = inner ℝ P.image (x - P.anchor)

/-- The actual trial observation satisfies its exact secant, scalar-defect
and anchor equations as soon as the starting cache is faithful. -/
theorem observedTrialPair_faithful (f : E → ℝ) (G : E → E) (S : State E)
    (hf : S.value = f S.point) (hg : S.gradient = G S.point) (s : E) :
    PairFaithful f G S.point (observedTrialPair f G S s) := by
  simp only [PairFaithful, observedTrialPair, hf, hg, sub_self, inner_zero_right, and_self]

/-- Anchor-pairing transport is exact after every real accepted move. -/
theorem PairFaithful.transport (f : E → ℝ) (G : E → E) (x s : E)
    (P : PairObservation E) (hP : PairFaithful f G x P) :
    PairFaithful f G (x + s) (P.transport s) := by
  refine ⟨hP.1, hP.2.1, ?_⟩
  change P.anchorPairing + inner ℝ P.image s = inner ℝ P.image (x + s - P.anchor)
  rw [hP.2.2]
  have he : x + s - P.anchor = (x - P.anchor) + s := by abel
  rw [he, inner_add_right]

/-- Conditional pair insertion preserves any property of all old entries
when the newly observed entry has that property. -/
theorem appendPositive_all (W : List (PairObservation E)) (P : PairObservation E)
    (Q : PairObservation E → Prop) (hW : ∀ a ∈ W, Q a) (hP : Q P) :
    ∀ a ∈ appendPositive W P, Q a := by
  classical
  unfold appendPositive
  split
  · intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact hW a ha
    · simpa only [List.mem_singleton.mp ha] using hP
  · exact hW

/-- Every retained pair of the concrete model was already observed; no
new secant or scalar is invented by rank or refutation cleanup. -/
theorem algorithmModel_pair_mem {n : ℕ} (P : Parameters)
    (S : State (EuclideanSpace ℝ (Fin n))) (a : PairObservation (EuclideanSpace ℝ (Fin n)))
    (ha : a ∈ (algorithmModel P S).pairs) : a ∈ S.pairs := by
  change a ∈ (rankWindow n S).drop (modelDeletion P (rankWindow n S)) at ha
  have hb := List.mem_of_mem_drop ha
  change a ∈ (retainNewest (min S.capacity n) S.pairs).drop
    (rankDeletion (retainNewest (min S.capacity n) S.pairs)) at hb
  exact List.mem_of_mem_drop (List.mem_of_mem_drop hb)

/-- Genuine observations remain genuine through every concrete ModelStep. -/
theorem algorithmModel_faithful {n : ℕ} (P : Parameters)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (S : State (EuclideanSpace ℝ (Fin n)))
    (hS : ∀ a ∈ S.pairs, PairFaithful f G S.point a) :
    ∀ a ∈ (algorithmModel P S).pairs, PairFaithful f G S.point a :=
  fun a ha => hS a (algorithmModel_pair_mem P S a ha)

/-- The one rejected probe is a genuine observation, and the second
ModelStep preserves the exact anchor equations at the unchanged point. -/
theorem outerSearch_faithful (model : State E → ModelResult E)
    (f : E → ℝ) (G : E → E)
    (hmodel : ∀ S : State E, (∀ a ∈ S.pairs, PairFaithful f G S.point a) →
      ∀ a ∈ (model S).pairs, PairFaithful f G S.point a)
    (sigma : ℝ) (S : State E) (hf : S.value = f S.point) (hg : S.gradient = G S.point)
    (hS : ∀ a ∈ S.pairs, PairFaithful f G S.point a) :
    ∀ a ∈ (outerSearch model f G sigma S).pairs, PairFaithful f G S.point a := by
  classical
  unfold outerSearch
  dsimp only
  split
  · exact hmodel S hS
  · apply hmodel
    exact appendPositive_all _ _ _ (hmodel S hS) (observedTrialPair_faithful f G S hf hg _)

/-- Exact endpoint data and anchor transport hold after every actual
accepted update, including the rejected-probe branch. -/
theorem outerAdvance_faithful (P : Parameters) (dimension : ℕ)
    (model : State E → ModelResult E) (f : E → ℝ) (G : E → E)
    (hmodel : ∀ S : State E, (∀ a ∈ S.pairs, PairFaithful f G S.point a) →
      ∀ a ∈ (model S).pairs, PairFaithful f G S.point a)
    (S : State E) (hf : S.value = f S.point) (hg : S.gradient = G S.point)
    (hS : ∀ a ∈ S.pairs, PairFaithful f G S.point a) :
    ∀ a ∈ (outerAdvance P dimension model f G S).pairs,
      PairFaithful f G (outerAdvance P dimension model f G S).point a := by
  classical
  unfold outerAdvance
  split
  · exact hS
  · dsimp only
    intro a ha
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    apply PairFaithful.transport
    exact appendPositive_all _ _ _
      (outerSearch_faithful model f G hmodel P.armijo S hf hg hS)
      (observedTrialPair_faithful f G S hf hg _) b hb

/-- Every pair stored by the complete literal XR algorithm is an actual
gradient secant with its true endpoint-value defect and exact current-anchor
pairing. There is no abstract oracle-data consistency assumption. -/
theorem algorithmRun_pairs_faithful {n : ℕ} (P : Parameters)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (x₀ : EuclideanSpace ℝ (Fin n)) (bounds : SpectralBounds) (k : ℕ) :
    ∀ a ∈ (algorithmRun P f G x₀ bounds k).pairs,
      PairFaithful f G (algorithmRun P f G x₀ bounds k).point a := by
  induction k with
  | zero => simp [algorithmRun, run, algorithmInitialState, initialState]
  | succ k ih =>
    have hc := run_cache_constants P n (algorithmModel P) f G
      (algorithmInitialState P f G x₀ bounds) rfl rfl k
    exact outerAdvance_faithful P n (algorithmModel P) f G
      (fun S hS => algorithmModel_faithful P f G S hS) _ hc.1 hc.2.1 ih

end
end krylov.XR
