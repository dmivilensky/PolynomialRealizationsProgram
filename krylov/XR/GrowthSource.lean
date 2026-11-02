import krylov.XR.GrowthPhase
import krylov.XR.CapacityGrowth

/-!
Article: main_krylov, thm:grow, primitive local source to actual memory growth.
Use: package the original analytic/independence/curvature assumptions,
then prove activation and the complete additive-capacity transition for
the literal algorithm. The source structure has no successful-test,
accepted-query, output-rate or eventual-window field.
Source: the genuine local activation theorems and actual numeric memory rule.
-/

namespace krylov.XR
noncomputable section
open Set Metric Filter Topology krylov.Methods
open scoped InnerProductSpace
variable {n : ℕ}
set_option maxHeartbeats 800000

/-- Primitive G1--G4 data. The trial hypotheses concern only partial
nonzero directions actually computed by the first ModelStep. Requiring
them only there suffices for the partial-memory transition theorem. -/
structure GrowthSource (P : Parameters)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (x₀ center : EuclideanSpace ℝ (Fin n)) (bounds : SpectralBounds) where
  mu : ℝ
  sigma : ℝ
  upper : ℝ
  ell : ℝ
  trialUpper : ℝ
  eta : ℝ
  mu_pos : 0 < mu
  sigma_pos : 0 < sigma
  upper_pos : 0 < upper
  ell_pos : 0 < ell
  trialUpper_pos : 0 < trialUpper
  eta_pos : 0 < eta
  f_deriv : ∀ᶠ z in 𝓝 center, HasFDerivAt f (innerSL ℝ (G z)) z
  g_deriv : ∀ᶠ z in 𝓝 center, HasFDerivAt G (H z) z
  h_cont : ∀ᶠ z in 𝓝 center, ContinuousAt H z
  coercive : ∀ v, mu * ‖v‖ ^ 2 ≤ inner ℝ v (H center v)
  h_norm : ‖H center‖ ≤ upper
  converges : Tendsto (fun k => (algorithmRun P f G x₀ bounds k).point) atTop (𝓝 center)
  distinct : ∀ k, (algorithmRun P f G x₀ bounds k).point ≠ center
  gainStart : ℕ
  gain : ∀ k, gainStart ≤ k →
    let W := incomingWindow (algorithmRun P f G x₀ bounds k)
    ∀ w : Fin W.length → ℝ, sigma ^ 2 * ‖WithLp.toLp 2 w‖ ^ 2 ≤
      ‖combine (krylov.Convergence.unitWindow (storedSteps W)) w‖ ^ 2
  trialStart : ℕ
  trial : ∀ k, trialStart ≤ k →
    let S := algorithmRun P f G x₀ bounds k
    let M := algorithmModel P S
    0 < M.pairs.length → M.pairs.length < n →
    modelDirection (storedSteps M.pairs) (storedImages M.pairs) (storedModel M.pairs) S.gradient ≠ 0 →
    ell * ‖modelDirection (storedSteps M.pairs) (storedImages M.pairs) (storedModel M.pairs) S.gradient‖ ^ 2 ≤
        algorithmComputedCurvature P S ∧
      algorithmComputedCurvature P S ≤ trialUpper *
        ‖modelDirection (storedSteps M.pairs) (storedImages M.pairs) (storedModel M.pairs) S.gradient‖ ^ 2 ∧
      inner ℝ (H center (modelDirection (storedSteps M.pairs) (storedImages M.pairs)
        (storedModel M.pairs) S.gradient))
        (modelDirection (storedSteps M.pairs) (storedImages M.pairs) (storedModel M.pairs) S.gradient) ≤
        (2 * (1 - P.armijo) - eta) * algorithmComputedCurvature P S
  safeguard_descent : (algorithmInitialState P f G x₀ bounds).descentConstant <
    dimensionDescentConstant n mu sigma upper trialUpper
  safeguard_norm : dimensionNormConstant n mu sigma upper ell <
    (algorithmInitialState P f G x₀ bounds).normConstant

variable {P : Parameters}
variable {f : EuclideanSpace ℝ (Fin n) → ℝ}
variable {G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
variable {H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
variable {x₀ center : EuclideanSpace ℝ (Fin n)} {bounds : SpectralBounds}

/-- Primitive source assumptions yield a genuine clean phase of the
actual executor, including exact memory and counter recurrences. -/
theorem GrowthSource.clean_phase (D : GrowthSource P f G H x₀ center bounds)
    (hP : P.Valid n) (hoff : P.valuesEnabled = false) :
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
  obtain ⟨K₁, hK₁⟩ := algorithmRun_eventually_first_accepted P hP hoff f G H x₀ center bounds
    D.f_deriv D.g_deriv D.h_cont D.mu D.sigma D.upper D.ell D.trialUpper D.eta
    D.mu_pos D.sigma_pos D.upper_pos D.ell_pos D.trialUpper_pos D.eta_pos
    D.coercive D.h_norm D.converges D.distinct D.gainStart D.gain D.trialStart D.trial
    D.safeguard_descent D.safeguard_norm
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
theorem GrowthSource.eventually_maximum_window (D : GrowthSource P f G H x₀ center bounds)
    (hP : P.Valid n) (hoff : P.valuesEnabled = false) :
    ∃ K, ∀ k, K ≤ k →
      let S := algorithmRun P f G x₀ bounds k
      S.capacity = P.maximumCapacity ∧
        (algorithmModel P S).pairs.length = P.maximumCapacity ∧
        (algorithmModel P S).deletedByTest = 0 ∧
        (algorithmModel P S).safeDirection S = (algorithmModel P S).direction ∧
        Accepted f P.armijo S.point S.gradient ((algorithmModel P S).safeDirection S) 1 := by
  obtain ⟨K₀, hK₀⟩ := D.clean_phase hP hoff
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
theorem GrowthSource.clean_pair_update (D : GrowthSource P f G H x₀ center bounds)
    (hP : P.Valid n) (hoff : P.valuesEnabled = false) :
    ∃ K, ∀ k, K ≤ k →
      let S := algorithmRun P f G x₀ bounds k
      let S' := algorithmRun P f G x₀ bounds (k + 1)
      let u := (algorithmModel P S).direction
      S'.point = S.point + u ∧
        S'.pairs = (incomingWindow S ++ [observedTrialPair f G S u]).map (fun a => a.transport u) := by
  obtain ⟨K₀, hK₀⟩ := D.clean_phase hP hoff
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

end
end krylov.XR
