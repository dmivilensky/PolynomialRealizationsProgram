import krylov.XR.LocalMemory
import krylov.XR.MemoryStateInvariants

/-!
Article: main_krylov, thm:grow, genuine eventual nonempty incoming memory.
Use: derive the first local window from actual positive accepted secants
and the literal capacity interval, before assuming any successful model
test. Source: original G1 data, real accepted observations and the memory rule.
-/

namespace krylov.XR
noncomputable section
open Set Metric Filter Topology
open scoped InnerProductSpace
variable {n : ℕ}

/-- Under G1 a genuine positive accepted pair is eventually appended at
every step, so the original incoming window is eventually nonempty. -/
theorem algorithmRun_eventually_incoming_nonempty (P : Parameters) (hP : P.Valid n)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (x₀ center : EuclideanSpace ℝ (Fin n)) (bounds : SpectralBounds)
    (hF : ∀ᶠ z in 𝓝 center, HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ᶠ z in 𝓝 center, HasFDerivAt G (H z) z) (hH : ContinuousAt H center)
    (mu : ℝ) (hmu : 0 < mu) (hpositive : ∀ v, mu * ‖v‖ ^ 2 ≤ inner ℝ v (H center v))
    (hconv : Tendsto (fun k => (algorithmRun P f G x₀ bounds k).point) atTop (𝓝 center))
    (hne : ∀ k, (algorithmRun P f G x₀ bounds k).point ≠ center) :
    ∃ K, ∀ k, K ≤ k → 0 < (incomingWindow (algorithmRun P f G x₀ bounds k)).length := by
  have hinit := algorithmRun_initial_gradient_ne_zero P f G x₀ center bounds hconv hne
  have hc := algorithmInitialState_constants P hP f G x₀ bounds hinit
  have hsig := hP.2.2.2.2.2.2.1
  have hsig₁ : P.armijo < 1 := hP.2.2.2.2.2.2.2.1.trans (by norm_num)
  obtain ⟨K, hK⟩ := run_eventually_local_new_pairs P n (algorithmModel P) f G H
    (algorithmInitialState P f G x₀ bounds) rfl rfl hc.1 hc.2 hsig hsig₁
    center hF hG hH mu hmu hpositive hconv hne 1 (by norm_num)
  have hn : 0 < n := by have := hP.1; have := hP.2.1; have := hP.2.2.1; omega
  refine ⟨K + 1, ?_⟩
  intro k hk
  cases k with
  | zero => omega
  | succ k =>
    have hnew := hK k (by omega)
    have hlen := outerAdvance_pairs_nonempty P n (algorithmModel P) f G
      (algorithmRun P f G x₀ bounds k) hnew.1 hnew.2.2.2
    have hmem := (algorithmRun_memory_invariants P hP f G x₀ bounds (k + 1)).1
    have hcap : 0 < (algorithmRun P f G x₀ bounds (k + 1)).capacity := by
      have := hP.1
      omega
    exact incomingWindow_nonempty _ hlen hcap hn

end
end krylov.XR
