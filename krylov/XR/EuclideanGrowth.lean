import krylov.XR.EuclideanGrowthSource
import krylov.XR.GrowthSource

/-!
Article: main_krylov, thm:grow and cor:xrF, actual Euclidean-split memory growth.
Use: apply the literal clean-step bookkeeping after source-derived selected
model acceptance, with either setting of the value flag. Inverse domains,
scalar gates and acceptance are proved from primitive source data.
Source: the actual safeguarded XR updates and finite capacity-growth rule.
-/

namespace krylov.XR
noncomputable section
open Set Metric Filter Topology krylov.Methods
open scoped InnerProductSpace
variable {n : ℕ} {P : Parameters}
variable {f : EuclideanSpace ℝ (Fin n) → ℝ}
variable {G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
variable {H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
variable {x₀ center : EuclideanSpace ℝ (Fin n)} {bounds : SpectralBounds}
set_option maxHeartbeats 800000

/-- Primitive source assumptions yield a genuine clean phase of the
actual executor, including exact memory and counter recurrences. -/
theorem EuclideanGrowthSource.clean_phase (D : EuclideanGrowthSource P f G H x₀ center bounds)
    (hP : P.Valid n) :
    ∃ K, ∀ k, K ≤ k →
      let S := euclideanAlgorithmRun P f G x₀ bounds k
      let S' := euclideanAlgorithmRun P f G x₀ bounds (k + 1)
      (euclideanAlgorithmModel P S).pairs = incomingWindow S ∧
        (euclideanAlgorithmModel P S).deletedByTest = 0 ∧
        (euclideanAlgorithmModel P S).safeDirection S = (euclideanAlgorithmModel P S).direction ∧
        Accepted f P.armijo S.point S.gradient ((euclideanAlgorithmModel P S).safeDirection S) 1 ∧
        S'.pairs.length = min S.capacity S.pairs.length + 1 ∧
        (S'.capacity, S'.cleanCount) = updateCapacity P n S.capacity S.cleanCount
          (min S.capacity S.pairs.length) 0 1 := by
  obtain ⟨K₁, hK₁⟩ := D.first_accepted hP
  obtain ⟨K₂, hK₂⟩ := euclideanAlgorithmRun_eventually_retains_window P hP f G H x₀ center bounds
    D.f_deriv D.g_deriv D.h_cont.self_of_nhds D.mu D.sigma D.mu_pos D.sigma_pos D.coercive
    D.converges D.distinct D.gainStart D.gain
  have hinit := euclideanAlgorithmRun_initial_gradient_ne_zero P f G x₀ center bounds D.converges D.distinct
  have hc := algorithmInitialState_constants P hP f G x₀ bounds hinit
  obtain ⟨K₃, hK₃⟩ := run_eventually_local_new_pairs P n (euclideanAlgorithmModel P) f G H
    (algorithmInitialState P f G x₀ bounds) rfl rfl hc.1 hc.2 hP.2.2.2.2.2.2.1
    (hP.2.2.2.2.2.2.2.1.trans (by norm_num)) center D.f_deriv D.g_deriv D.h_cont.self_of_nhds
    D.mu D.mu_pos D.coercive D.converges D.distinct 1 (by norm_num)
  refine ⟨max K₁ (max K₂ K₃), ?_⟩
  intro k hk
  let S := euclideanAlgorithmRun P f G x₀ bounds k
  let S' := euclideanAlgorithmRun P f G x₀ bounds (k + 1)
  let M := euclideanAlgorithmModel P S
  have hfirst := hK₁ k (by omega)
  have hretain := hK₂ k (by omega)
  have hnew := hK₃ k (by omega)
  dsimp only at hfirst hretain hnew ⊢
  have hsearch := outerSearch_first_accepted (euclideanAlgorithmModel P) f G P.armijo S hfirst.2
  have hpositive : positivePair (observedTrialPair f G S (M.safeDirection S)) := by
    have hh : positivePair (observedTrialPair f G S
      ((outerSearch (euclideanAlgorithmModel P) f G P.armijo S).length •
        (outerSearch (euclideanAlgorithmModel P) f G P.armijo S).direction)) := hnew.2.2.2
    rw [hsearch] at hh
    simpa only [one_smul] using hh
  have hupdate := outerAdvance_clean_update P n (euclideanAlgorithmModel P) f G S hnew.1 hfirst.2 hpositive
  have hcap : S.capacity ≤ n := ((euclideanAlgorithmRun_memory_invariants P hP f G x₀ bounds k).2.1).trans hP.2.2.1
  have hcount : (incomingWindow S).length = min S.capacity S.pairs.length := by
    simp only [incomingWindow, retainNewest_length, min_eq_left hcap]
  refine ⟨hretain.2.1, hretain.2.2.2, hfirst.1, hfirst.2, ?_, ?_⟩
  · have hpairs := hupdate.2.1
    change S'.pairs = _ at hpairs
    rw [hpairs, List.length_map, List.length_append, List.length_singleton, hretain.2.1, hcount]
  · have hcounter := hupdate.2.2
    change (S'.capacity, S'.cleanCount) = updateCapacity P n S.capacity S.cleanCount
      M.pairsBeforeTest M.deletedByTest 1 at hcounter
    have hp1 : M.pairsBeforeTest = min S.capacity S.pairs.length := hretain.2.2.1.trans hcount
    have ho : M.deletedByTest = 0 := hretain.2.2.2
    rw [hp1, ho] at hcounter
    exact hcounter

/-- The actual source-driven algorithm reaches its maximum permitted
window and capacity. This is derived from the literal memory recurrence. -/
theorem EuclideanGrowthSource.eventually_maximum_window (D : EuclideanGrowthSource P f G H x₀ center bounds)
    (hP : P.Valid n) :
    ∃ K, ∀ k, K ≤ k →
      let S := euclideanAlgorithmRun P f G x₀ bounds k
      S.capacity = P.maximumCapacity ∧
        (euclideanAlgorithmModel P S).pairs.length = P.maximumCapacity ∧
        (euclideanAlgorithmModel P S).deletedByTest = 0 ∧
        (euclideanAlgorithmModel P S).safeDirection S = (euclideanAlgorithmModel P S).direction ∧
        Accepted f P.armijo S.point S.gradient ((euclideanAlgorithmModel P S).safeDirection S) 1 := by
  obtain ⟨K₀, hK₀⟩ := D.clean_phase hP
  obtain ⟨K₁, hK₁⟩ := capacity_growth_eventually_of_tail P n K₀ (by have := hP.1; omega)
    hP.2.2.1 (by have := hP.2.2.2.1; omega)
    (fun k => (euclideanAlgorithmRun P f G x₀ bounds k).capacity)
    (fun k => (euclideanAlgorithmRun P f G x₀ bounds k).cleanCount)
    (fun k => (euclideanAlgorithmRun P f G x₀ bounds k).pairs.length)
    (fun k => (euclideanAlgorithmRun_memory_invariants P hP f G x₀ bounds k).2.1)
    (fun k => (euclideanAlgorithmRun_memory_invariants P hP f G x₀ bounds k).2.2)
    (fun k hk => (hK₀ k hk).2.2.2.2.1)
    (fun k hk => (hK₀ k hk).2.2.2.2.2)
  refine ⟨max K₀ K₁, ?_⟩
  intro k hk
  have hh := hK₀ k (by omega)
  have hc := hK₁ k (by omega)
  dsimp only at hh hc ⊢
  refine ⟨hc.1, ?_, hh.2.1, hh.2.2.1, hh.2.2.2.1⟩
  rw [hh.1]
  simp only [incomingWindow, retainNewest_length, hc.1, min_eq_left hP.2.2.1, min_eq_left hc.2]

/-- Exact genuine observations on the source-derived clean phase, for
the chronological SS1 dictionary. The newly appended pair is computed
from actual f/G and its positivity is derived from G1. -/
theorem EuclideanGrowthSource.clean_pair_update (D : EuclideanGrowthSource P f G H x₀ center bounds)
    (hP : P.Valid n) :
    ∃ K, ∀ k, K ≤ k →
      let S := euclideanAlgorithmRun P f G x₀ bounds k
      let S' := euclideanAlgorithmRun P f G x₀ bounds (k + 1)
      let u := (euclideanAlgorithmModel P S).direction
      S'.point = S.point + u ∧
        S'.pairs = (incomingWindow S ++ [observedTrialPair f G S u]).map (fun a => a.transport u) := by
  obtain ⟨K₀, hK₀⟩ := D.clean_phase hP
  have hinit := euclideanAlgorithmRun_initial_gradient_ne_zero P f G x₀ center bounds D.converges D.distinct
  have hc := algorithmInitialState_constants P hP f G x₀ bounds hinit
  obtain ⟨K₁, hK₁⟩ := run_eventually_local_new_pairs P n (euclideanAlgorithmModel P) f G H
    (algorithmInitialState P f G x₀ bounds) rfl rfl hc.1 hc.2 hP.2.2.2.2.2.2.1
    (hP.2.2.2.2.2.2.2.1.trans (by norm_num)) center D.f_deriv D.g_deriv D.h_cont.self_of_nhds
    D.mu D.mu_pos D.coercive D.converges D.distinct 1 (by norm_num)
  refine ⟨max K₀ K₁, ?_⟩
  intro k hk
  let S := euclideanAlgorithmRun P f G x₀ bounds k
  let S' := euclideanAlgorithmRun P f G x₀ bounds (k + 1)
  let M := euclideanAlgorithmModel P S
  have hh := hK₀ k (by omega)
  have hnew := hK₁ k (by omega)
  dsimp only at hh hnew ⊢
  have hsearch := outerSearch_first_accepted (euclideanAlgorithmModel P) f G P.armijo S hh.2.2.2.1
  have hpositive : positivePair (observedTrialPair f G S (M.safeDirection S)) := by
    have hp : positivePair (observedTrialPair f G S
      ((outerSearch (euclideanAlgorithmModel P) f G P.armijo S).length •
        (outerSearch (euclideanAlgorithmModel P) f G P.armijo S).direction)) := hnew.2.2.2
    rw [hsearch] at hp
    simpa only [one_smul] using hp
  have hu := outerAdvance_clean_update P n (euclideanAlgorithmModel P) f G S hnew.1 hh.2.2.2.1 hpositive
  have hs : M.safeDirection S = M.direction := hh.2.2.1
  have hp : M.pairs = incomingWindow S := hh.1
  change S'.point = S.point + M.direction ∧
    S'.pairs = (incomingWindow S ++ [observedTrialPair f G S M.direction]).map (fun a => a.transport M.direction)
  constructor
  · exact hu.1.trans (congrArg (S.point + ·) hs)
  · have hw := hu.2.1
    change S'.pairs = (M.pairs ++ [observedTrialPair f G S (M.safeDirection S)]).map
      (fun a => a.transport (M.safeDirection S)) at hw
    rwa [hs, hp] at hw


/-- Both actual value gates and exact corrected-model selection hold on
the primitive source tail whenever the value flag is enabled. -/
theorem EuclideanGrowthSource.corrected_gates (D : EuclideanGrowthSource P f G H x₀ center bounds)
    (hP : P.Valid n) (hon : P.valuesEnabled = true) :
    ∃ K, ∀ k, K ≤ k →
      let W := (euclideanAlgorithmModel P (euclideanAlgorithmRun P f G x₀ bounds k)).pairs
      (∀ i : Fin W.length, |12 * euclideanStoredSplit (euclideanAlgorithmRun P f G x₀ bounds k).point W i * (W.get i).valueDefect| ≤ storedPairing W i i / 2) ∧
        euclideanCorrectedWindowPasses P.windowThreshold (euclideanAlgorithmRun P f G x₀ bounds k).point W ∧ selectedEuclideanModel P (euclideanAlgorithmRun P f G x₀ bounds k).point W = euclideanStoredValueModel (euclideanAlgorithmRun P f G x₀ bounds k).point W :=
  D.corrected_selection hP hon

end
end krylov.XR
