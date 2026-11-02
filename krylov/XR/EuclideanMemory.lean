import krylov.XR.EuclideanModelBasic
import krylov.XR.MemoryObservations
import krylov.XR.MemoryPositive
import krylov.XR.MemoryStateInvariants

/-!
Article: main_krylov, cor:xrF and the G1--G4 activation proof.
Use: the literal Euclidean-split executor stores genuine positive observations
and obeys exactly the original suffix and capacity rules.
Source: the unchanged scalar executor and chronological memory operations.
-/

namespace krylov.XR
noncomputable section
open scoped InnerProductSpace
variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

theorem euclideanAlgorithmModel_pairs_drop (P : Parameters) (S : State E) :
    (euclideanAlgorithmModel P S).pairs = S.pairs.drop (modelDropCount P S) :=
  algorithmModel_pairs_drop P S

/-- Every real Euclidean-split observation has its actual scalar and gradient data. -/
theorem euclideanAlgorithmRun_pairs_faithful (P : Parameters) (f : E → ℝ) (G : E → E)
    (x₀ : E) (bounds : SpectralBounds) (k : ℕ) :
    ∀ a ∈ (euclideanAlgorithmRun P f G x₀ bounds k).pairs,
      PairFaithful f G (euclideanAlgorithmRun P f G x₀ bounds k).point a := by
  induction k with
  | zero => simp [euclideanAlgorithmRun, run, algorithmInitialState, initialState]
  | succ k ih =>
    have hc := run_cache_constants P n (euclideanAlgorithmModel P) f G
      (algorithmInitialState P f G x₀ bounds) rfl rfl k
    exact outerAdvance_faithful P n (euclideanAlgorithmModel P) f G
      (fun S hS a ha => hS a (euclideanAlgorithmModel_pair_mem P S a ha))
      _ hc.1 hc.2.1 ih

/-- Positivity comes from the genuine insertion guard, including rejected probes. -/
theorem euclideanAlgorithmRun_pairs_positive (P : Parameters) (f : E → ℝ) (G : E → E)
    (x₀ : E) (bounds : SpectralBounds) (k : ℕ) :
    ∀ a ∈ (euclideanAlgorithmRun P f G x₀ bounds k).pairs, positivePair a := by
  induction k with
  | zero => simp [euclideanAlgorithmRun, run, algorithmInitialState, initialState]
  | succ k ih =>
    exact outerAdvance_positive P n (euclideanAlgorithmModel P)
      (fun S hS a ha => hS a (euclideanAlgorithmModel_pair_mem P S a ha)) f G _ ih

/-- The actual capacity and clean counter stay in their configured domains. -/
theorem euclideanAlgorithmRun_memory_invariants (P : Parameters) (hP : P.Valid n)
    (f : E → ℝ) (G : E → E) (x₀ : E) (bounds : SpectralBounds) (k : ℕ) :
    P.initialCapacity ≤ (euclideanAlgorithmRun P f G x₀ bounds k).capacity ∧
      (euclideanAlgorithmRun P f G x₀ bounds k).capacity ≤ P.maximumCapacity ∧
      (euclideanAlgorithmRun P f G x₀ bounds k).cleanCount < P.cleanPeriod := by
  have hmax : P.initialCapacity ≤ P.maximumCapacity := hP.2.1
  have hq : 0 < P.cleanPeriod := by have := hP.2.2.2.1; omega
  induction k with
  | zero => exact ⟨le_rfl, hmax, hq⟩
  | succ k ih =>
    exact outerAdvance_memory_invariants P n (euclideanAlgorithmModel P) f G _ ih.1 ih.2.1 hq ih.2.2

end
end krylov.XR
