import krylov.XR.CorrectedGrowthSource
import krylov.XR.GrowthSource

/-!
Article: main_krylov, thm:grow and cor:xrF, actual selected-model memory growth.
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
theorem SelectedGrowthSource.clean_phase (D : SelectedGrowthSource P f G H x₀ center bounds)
    (hP : P.Valid n) :
    ∃ K, ∀ k, K ≤ k →
      let S := algorithmRun P f G x₀ bounds k
      let S' := algorithmRun P f G x₀ bounds (k + 1)
      (algorithmModel P S).pairs = incomingWindow S ∧
        (algorithmModel P S).deletedByTest = 0 ∧
        (algorithmModel P S).safeDirection S = (algorithmModel P S).direction ∧
        Accepted f P.armijo S.point S.gradient ((algorithmModel P S).safeDirection S) 1 ∧
        S'.pairs.length = min S.capacity S.pairs.length + 1 ∧
        (S'.capacity, S'.cleanCount) = updateCapacity P n S.capacity S.cleanCount
          (min S.capacity S.pairs.length) 0 1 := by
  obtain ⟨K₁, hK₁⟩ := D.first_accepted hP
  obtain ⟨K₂, hK₂⟩ := algorithmRun_eventually_retains_window P hP f G H x₀ center bounds
    D.f_deriv D.g_deriv D.h_cont.self_of_nhds D.mu D.sigma D.mu_pos D.sigma_pos D.coercive
    D.converges D.distinct D.gainStart D.gain
  have hinit := algorithmRun_initial_gradient_ne_zero P f G x₀ center bounds D.converges D.distinct
  have hc := algorithmInitialState_constants P hP f G x₀ bounds hinit
  obtain ⟨K₃, hK₃⟩ := run_eventually_local_new_pairs P n (algorithmModel P) f G H
    (algorithmInitialState P f G x₀ bounds) rfl rfl hc.1 hc.2 hP.2.2.2.2.2.2.1
    (hP.2.2.2.2.2.2.2.1.trans (by norm_num)) center D.f_deriv D.g_deriv D.h_cont.self_of_nhds
    D.mu D.mu_pos D.coercive D.converges D.distinct 1 (by norm_num)
  refine ⟨max K₁ (max K₂ K₃), ?_⟩
  intro k hk
  let S := algorithmRun P f G x₀ bounds k
  let S' := algorithmRun P f G x₀ bounds (k + 1)
  let M := algorithmModel P S
  have hfirst := hK₁ k (by omega)
  have hretain := hK₂ k (by omega)
  have hnew := hK₃ k (by omega)
  dsimp only at hfirst hretain hnew ⊢
  have hsearch := outerSearch_first_accepted (algorithmModel P) f G P.armijo S hfirst.2
  have hpositive : positivePair (observedTrialPair f G S (M.safeDirection S)) := by
    have hh : positivePair (observedTrialPair f G S
      ((outerSearch (algorithmModel P) f G P.armijo S).length •
        (outerSearch (algorithmModel P) f G P.armijo S).direction)) := hnew.2.2.2
    rw [hsearch] at hh
    simpa only [one_smul] using hh
  have hupdate := outerAdvance_clean_update P n (algorithmModel P) f G S hnew.1 hfirst.2 hpositive
  have hcap : S.capacity ≤ n := ((algorithmRun_memory_invariants P hP f G x₀ bounds k).2.1).trans hP.2.2.1
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
theorem SelectedGrowthSource.eventually_maximum_window (D : SelectedGrowthSource P f G H x₀ center bounds)
    (hP : P.Valid n) :
    ∃ K, ∀ k, K ≤ k →
      let S := algorithmRun P f G x₀ bounds k
      S.capacity = P.maximumCapacity ∧
        (algorithmModel P S).pairs.length = P.maximumCapacity ∧
        (algorithmModel P S).deletedByTest = 0 ∧
        (algorithmModel P S).safeDirection S = (algorithmModel P S).direction ∧
        Accepted f P.armijo S.point S.gradient ((algorithmModel P S).safeDirection S) 1 := by
  obtain ⟨K₀, hK₀⟩ := D.clean_phase hP
  obtain ⟨K₁, hK₁⟩ := capacity_growth_eventually_of_tail P n K₀ (by have := hP.1; omega)
    hP.2.2.1 (by have := hP.2.2.2.1; omega)
    (fun k => (algorithmRun P f G x₀ bounds k).capacity)
    (fun k => (algorithmRun P f G x₀ bounds k).cleanCount)
    (fun k => (algorithmRun P f G x₀ bounds k).pairs.length)
    (fun k => (algorithmRun_memory_invariants P hP f G x₀ bounds k).2.1)
    (fun k => (algorithmRun_memory_invariants P hP f G x₀ bounds k).2.2)
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
theorem SelectedGrowthSource.clean_pair_update (D : SelectedGrowthSource P f G H x₀ center bounds)
    (hP : P.Valid n) :
    ∃ K, ∀ k, K ≤ k →
      let S := algorithmRun P f G x₀ bounds k
      let S' := algorithmRun P f G x₀ bounds (k + 1)
      let u := (algorithmModel P S).direction
      S'.point = S.point + u ∧
        S'.pairs = (incomingWindow S ++ [observedTrialPair f G S u]).map (fun a => a.transport u) := by
  obtain ⟨K₀, hK₀⟩ := D.clean_phase hP
  have hinit := algorithmRun_initial_gradient_ne_zero P f G x₀ center bounds D.converges D.distinct
  have hc := algorithmInitialState_constants P hP f G x₀ bounds hinit
  obtain ⟨K₁, hK₁⟩ := run_eventually_local_new_pairs P n (algorithmModel P) f G H
    (algorithmInitialState P f G x₀ bounds) rfl rfl hc.1 hc.2 hP.2.2.2.2.2.2.1
    (hP.2.2.2.2.2.2.2.1.trans (by norm_num)) center D.f_deriv D.g_deriv D.h_cont.self_of_nhds
    D.mu D.mu_pos D.coercive D.converges D.distinct 1 (by norm_num)
  refine ⟨max K₀ K₁, ?_⟩
  intro k hk
  let S := algorithmRun P f G x₀ bounds k
  let S' := algorithmRun P f G x₀ bounds (k + 1)
  let M := algorithmModel P S
  have hh := hK₀ k (by omega)
  have hnew := hK₁ k (by omega)
  dsimp only at hh hnew ⊢
  have hsearch := outerSearch_first_accepted (algorithmModel P) f G P.armijo S hh.2.2.2.1
  have hpositive : positivePair (observedTrialPair f G S (M.safeDirection S)) := by
    have hp : positivePair (observedTrialPair f G S
      ((outerSearch (algorithmModel P) f G P.armijo S).length •
        (outerSearch (algorithmModel P) f G P.armijo S).direction)) := hnew.2.2.2
    rw [hsearch] at hp
    simpa only [one_smul] using hp
  have hu := outerAdvance_clean_update P n (algorithmModel P) f G S hnew.1 hh.2.2.2.1 hpositive
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
theorem SelectedGrowthSource.corrected_gates (D : SelectedGrowthSource P f G H x₀ center bounds)
    (hP : P.Valid n) (hon : P.valuesEnabled = true) :
    ∃ K, ∀ k, K ≤ k →
      let W := (algorithmModel P (algorithmRun P f G x₀ bounds k)).pairs
      (∀ i : Fin W.length, |12 * storedSplit W i * (W.get i).valueDefect| ≤ storedPairing W i i / 2) ∧
        correctedWindowPasses P.windowThreshold W ∧ selectedModel P W = storedValueModel W :=
  algorithmRun_eventually_corrected_gates P hP hon f G H x₀ center bounds D.f_deriv D.g_deriv
    D.h_cont.self_of_nhds D.sourceRadius D.sourceRadius_pos D.hessianLipschitz D.h_lip D.mu D.sigma
    D.mu_pos D.sigma_pos D.coercive D.converges D.distinct D.gainStart D.gain

end
end krylov.XR
