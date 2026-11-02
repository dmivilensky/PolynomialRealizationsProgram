import krylov.XR.EuclideanFullMemory
import krylov.XR.EuclideanGrowthSource

/-!
Article: main_krylov, thm:grow, the m0=n exception to G3.
Use: prove full-window entry from G1 and G2 alone, through both genuine
ModelSteps and real backtracking. Once full dimension is reached the
partial-window trial condition is vacuous, so the proved local transition
uses G4 without ever assuming adequacy of a partial trial.
Source: actual positive observations, pre-cleanup independence and finite
memory filling of the literal executor.
-/

namespace krylov.XR
noncomputable section
open Set Metric Filter Topology krylov.Methods
open scoped InnerProductSpace
variable {n : ℕ}
set_option maxHeartbeats 800000

/-- Full initial capacity reaches an actual full retained window from
G1 and G2, without any assumption about the computed trial curvature. -/
theorem euclideanAlgorithmRun_eventually_full_of_initial_full (P : Parameters) (hP : P.Valid n)
    (hfull : P.initialCapacity = n)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (x₀ center : EuclideanSpace ℝ (Fin n)) (bounds : SpectralBounds)
    (hF : ∀ᶠ z in 𝓝 center, HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ᶠ z in 𝓝 center, HasFDerivAt G (H z) z) (hH : ContinuousAt H center)
    (mu sigma : ℝ) (hmu : 0 < mu) (hsigma : 0 < sigma)
    (hpositive : ∀ v, mu * ‖v‖ ^ 2 ≤ inner ℝ v (H center v))
    (hconv : Tendsto (fun k => (euclideanAlgorithmRun P f G x₀ bounds k).point) atTop (𝓝 center))
    (hne : ∀ k, (euclideanAlgorithmRun P f G x₀ bounds k).point ≠ center)
    (K₀ : ℕ)
    (hgain : ∀ k, K₀ ≤ k →
      let W := incomingWindow (euclideanAlgorithmRun P f G x₀ bounds k)
      ∀ w : Fin W.length → ℝ, sigma ^ 2 * ‖WithLp.toLp 2 w‖ ^ 2 ≤
        ‖combine (krylov.Convergence.unitWindow (storedSteps W)) w‖ ^ 2)
    (hprobeGain : ∀ k, K₀ ≤ k →
      let S := euclideanAlgorithmRun P f G x₀ bounds k
      ¬Accepted f P.armijo S.point S.gradient ((euclideanAlgorithmModel P S).safeDirection S) 1 →
      let W := incomingWindow (firstProbeState (euclideanAlgorithmModel P) f G S)
      ∀ w : Fin W.length → ℝ, sigma ^ 2 * ‖WithLp.toLp 2 w‖ ^ 2 ≤
        ‖combine (krylov.Convergence.unitWindow (storedSteps W)) w‖ ^ 2) :
    ∃ K, ∀ k, K ≤ k → (euclideanAlgorithmModel P (euclideanAlgorithmRun P f G x₀ bounds k)).pairs.length = n := by
  obtain ⟨K₁, hK₁⟩ := euclideanAlgorithmRun_eventually_retains_window P hP f G H x₀ center bounds
    hF hG hH mu sigma hmu hsigma hpositive hconv hne K₀ hgain
  obtain ⟨K₂, hK₂⟩ := euclideanAlgorithmRun_eventually_probe_retains_window P hP f G H x₀ center bounds
    hF hG hH mu sigma hmu hsigma hpositive hconv hne K₀ hprobeGain
  have hinit := euclideanAlgorithmRun_initial_gradient_ne_zero P f G x₀ center bounds hconv hne
  have hc := algorithmInitialState_constants P hP f G x₀ bounds hinit
  obtain ⟨K₃, hK₃⟩ := run_eventually_local_new_pairs P n (euclideanAlgorithmModel P) f G H
    (algorithmInitialState P f G x₀ bounds) rfl rfl hc.1 hc.2 hP.2.2.2.2.2.2.1
    (hP.2.2.2.2.2.2.2.1.trans (by norm_num)) center hF hG hH mu hmu hpositive hconv hne 1 (by norm_num)
  let K := max K₁ (max K₂ K₃)
  have hcap (k : ℕ) : (euclideanAlgorithmRun P f G x₀ bounds k).capacity = n := by
    have hh := euclideanAlgorithmRun_memory_invariants P hP f G x₀ bounds k
    have hi := hP.2.2.1
    rw [hfull] at hh
    omega
  have hstep (k : ℕ) (hk : K ≤ k) :
      min n (euclideanAlgorithmRun P f G x₀ bounds k).pairs.length + 1 ≤
        (euclideanAlgorithmRun P f G x₀ bounds (k + 1)).pairs.length := by
    have hfirst := (hK₁ k (by dsimp only [K] at hk; omega)).2.1
    have hnew := hK₃ k (by dsimp only [K] at hk; omega)
    exact euclideanOuterAdvance_full_length_ge P f G _ hnew.1 (hcap k) hfirst
      (fun hr => (hK₂ k (by dsimp only [K] at hk; omega) hr).2.1) hnew.2.2.2
  have hfilled := length_fills_of_tail (fun k => (euclideanAlgorithmRun P f G x₀ bounds k).pairs.length) n K hstep
  refine ⟨K + n, ?_⟩
  intro k hk
  rw [(hK₁ k (by dsimp only [K] at hk; omega)).2.1]
  simp only [incomingWindow, retainNewest_length, hcap k, min_self, min_eq_left (hfilled k hk)]


end
end krylov.XR
