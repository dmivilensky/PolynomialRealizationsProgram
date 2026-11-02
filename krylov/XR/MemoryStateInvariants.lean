import krylov.XR.MemoryCapacity
import krylov.XR.MemorySuffix
import krylov.XR.LocalModelActivation

/-!
Article: main_krylov, alg:xr and thm:grow, actual memory-state invariants.
Use: carry the proved capacity/clean-counter rules through real recursive
execution and prove that a genuinely inserted accepted pair makes the next
incoming window nonempty. Source: the literal counter update and suffix
length, without an assumed eventual full-window state.
-/

namespace krylov.XR
noncomputable section
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Real accepted or stopped updates preserve the configured capacity
interval and the clean-counter trigger bound. -/
theorem outerAdvance_memory_invariants (P : Parameters) (dimension : ℕ)
    (model : State E → ModelResult E) (f : E → ℝ) (G : E → E) (S : State E)
    (hlo : P.initialCapacity ≤ S.capacity) (hhi : S.capacity ≤ P.maximumCapacity)
    (hq : 0 < P.cleanPeriod) (hclean : S.cleanCount < P.cleanPeriod) :
    P.initialCapacity ≤ (outerAdvance P dimension model f G S).capacity ∧
      (outerAdvance P dimension model f G S).capacity ≤ P.maximumCapacity ∧
      (outerAdvance P dimension model f G S).cleanCount < P.cleanPeriod := by
  classical
  unfold outerAdvance
  split
  · exact ⟨hlo, hhi, hclean⟩
  · dsimp only
    exact ⟨(updateCapacity_interval P dimension _ _ _ _ _ hlo hhi).1,
      (updateCapacity_interval P dimension _ _ _ _ _ hlo hhi).2,
      updateCapacity_clean_lt P dimension _ _ _ _ _ hq hclean⟩

/-- The literal full algorithm always has valid capacity and counter
states, including all rejected-probe and stationary branches. -/
theorem algorithmRun_memory_invariants {n : ℕ} (P : Parameters) (hP : P.Valid n)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (x₀ : EuclideanSpace ℝ (Fin n)) (bounds : SpectralBounds) (k : ℕ) :
    P.initialCapacity ≤ (algorithmRun P f G x₀ bounds k).capacity ∧
      (algorithmRun P f G x₀ bounds k).capacity ≤ P.maximumCapacity ∧
      (algorithmRun P f G x₀ bounds k).cleanCount < P.cleanPeriod := by
  have hmax : P.initialCapacity ≤ P.maximumCapacity := hP.2.1
  have hq : 0 < P.cleanPeriod := by have := hP.2.2.2.1; omega
  induction k with
  | zero => exact ⟨le_rfl, hmax, hq⟩
  | succ k ih => exact outerAdvance_memory_invariants P n (algorithmModel P) f G _ ih.1 ih.2.1 hq ih.2.2

/-- A positive actually accepted pair makes post-update memory nonempty,
regardless of how many older pairs the model retained. -/
theorem outerAdvance_pairs_nonempty (P : Parameters) (dimension : ℕ)
    (model : State E → ModelResult E) (f : E → ℝ) (G : E → E) (S : State E)
    (hg : S.gradient ≠ 0)
    (hpositive : positivePair (observedTrialPair f G S
      ((outerSearch model f G P.armijo S).length • (outerSearch model f G P.armijo S).direction))) :
    0 < (outerAdvance P dimension model f G S).pairs.length := by
  classical
  simp only [outerAdvance, ite_eq_right hg]
  rw [List.length_map]
  unfold appendPositive
  rw [ite_eq_left hpositive, List.length_append, List.length_singleton]
  omega

/-- Any nonempty actual stored list gives a nonempty incoming window
when the configured capacity and physical dimension are positive. -/
theorem incomingWindow_nonempty {n : ℕ} (S : State (EuclideanSpace ℝ (Fin n)))
    (hS : 0 < S.pairs.length) (hcap : 0 < S.capacity) (hn : 0 < n) :
    0 < (incomingWindow S).length := by
  simp only [incomingWindow, retainNewest_length]
  omega

end
end krylov.XR
