import krylov.XR.EuclideanPracticalModel
import krylov.XR.CorrectedGrowth
import krylov.XR.GrowthFullSource

/-!
# Local memory of the practical XR execution

Article Theorem 7.3 (`thm:grow`) and Corollary 7.4 (`cor:xrF`).
The trial policy changes scalar curvature but leaves chronological suffix
selection unchanged. The generic executor lemmas therefore supply genuine
observations, finite forgetting and local secant errors for `euclideanPracticalRun`.
No eventual acceptance, retention or convergence rate is assumed here.
-/

namespace krylov.XR
noncomputable section
open Set Metric Filter Topology krylov.Methods
open scoped InnerProductSpace NNReal
variable {n : ℕ}

/-- The practical model retains exactly the same observed suffix. -/
theorem euclideanPracticalModel_pairs_drop (P : Parameters)
    (S : State (EuclideanSpace ℝ (Fin n))) :
    (euclideanPracticalModel P S).pairs = S.pairs.drop (modelDropCount P S) :=
  algorithmModel_pairs_drop P S

/-- The retained physical steps are independent after exact rank cleanup. -/
theorem euclideanPracticalModel_independent (P : Parameters)
    (S : State (EuclideanSpace ℝ (Fin n))) :
    LinearIndependent ℝ (storedSteps (euclideanPracticalModel P S).pairs) :=
  algorithmModel_independent P S

/-- Selection neither invents observations nor exceeds the memory cap. -/
theorem euclideanPracticalModel_pair_mem (P : Parameters)
    (S : State (EuclideanSpace ℝ (Fin n)))
    (a : PairObservation (EuclideanSpace ℝ (Fin n)))
    (ha : a ∈ (euclideanPracticalModel P S).pairs) : a ∈ S.pairs :=
  algorithmModel_pair_mem P S a ha

/-- The model's retained length obeys the common capacity/dimension bound. -/
theorem euclideanPracticalModel_length_le (P : Parameters)
    (S : State (EuclideanSpace ℝ (Fin n))) :
    (euclideanPracticalModel P S).pairs.length ≤ min S.capacity n :=
  algorithmModel_length_le P S

/-- Memory counters remain in the actual configured intervals. -/
theorem euclideanPracticalRun_memory_invariants (P : Parameters) (hP : P.Valid n)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (x₀ : EuclideanSpace ℝ (Fin n)) (k : ℕ) :
    P.initialCapacity ≤ (euclideanPracticalRun P f G x₀ k).capacity ∧
      (euclideanPracticalRun P f G x₀ k).capacity ≤ P.maximumCapacity ∧
      (euclideanPracticalRun P f G x₀ k).cleanCount < P.cleanPeriod := by
  have hq : 0 < P.cleanPeriod := by have := hP.2.2.2.1; omega
  induction k with
  | zero => exact ⟨le_rfl, hP.2.1, hq⟩
  | succ k ih =>
    exact outerAdvance_memory_invariants P n (euclideanPracticalModel P) f G _ ih.1 ih.2.1 hq ih.2.2

/-- All actual practical observations are positive-curvature pairs. -/
theorem euclideanPracticalRun_pairs_positive (P : Parameters)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (x₀ : EuclideanSpace ℝ (Fin n)) (k : ℕ) :
    ∀ a ∈ (euclideanPracticalRun P f G x₀ k).pairs, positivePair a := by
  induction k with
  | zero => simp [euclideanPracticalRun, run, algorithmInitialState, initialState]
  | succ k ih =>
    apply outerAdvance_positive P n (euclideanPracticalModel P) _ f G _ ih
    intro S hS a ha
    exact hS a (euclideanPracticalModel_pair_mem P S a ha)

/-- Every stored endpoint value, secant and transported covector is genuine. -/
theorem euclideanPracticalRun_pairs_faithful (P : Parameters)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (x₀ : EuclideanSpace ℝ (Fin n)) (k : ℕ) :
    ∀ a ∈ (euclideanPracticalRun P f G x₀ k).pairs,
      PairFaithful f G (euclideanPracticalRun P f G x₀ k).point a := by
  induction k with
  | zero => simp [euclideanPracticalRun, run, algorithmInitialState, initialState]
  | succ k ih =>
    have hc := run_cache_constants P n (euclideanPracticalModel P) f G
      (algorithmInitialState P f G x₀ none) rfl rfl k
    exact outerAdvance_faithful P n (euclideanPracticalModel P) f G
      (fun S hS a ha => hS a (euclideanPracticalModel_pair_mem P S a ha)) _ hc.1 hc.2.1 ih

/-- A nonstationary accepted trajectory converging to its distinct limit
cannot have started with a zero gradient in the literal stopped executor. -/
theorem euclideanPracticalRun_initial_gradient_ne_zero (P : Parameters)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (x₀ center : EuclideanSpace ℝ (Fin n))
    (hconv : Tendsto (fun k => (euclideanPracticalRun P f G x₀ k).point) atTop (𝓝 center))
    (hne : ∀ k, (euclideanPracticalRun P f G x₀ k).point ≠ center) : G x₀ ≠ 0 := by
  intro hzero
  have hr k : euclideanPracticalRun P f G x₀ k = algorithmInitialState P f G x₀ none :=
    run_stationary P n (euclideanPracticalModel P) f G _ hzero k
  have hconst : Tendsto (fun k => (euclideanPracticalRun P f G x₀ k).point) atTop (𝓝 x₀) := by
    simpa only [hr, algorithmInitialState, initialState] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => x₀) atTop (𝓝 x₀))
  have heq : x₀ = center := tendsto_nhds_unique hconst hconv
  exact hne 0 heq

/-- Every genuine stored segment of literal XR is eventually contained
in any prescribed neighbourhood of the accepted nondegenerate limit. -/
theorem euclideanPracticalRun_eventually_local_pairs (P : Parameters) (hP : P.Valid n)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (x₀ center : EuclideanSpace ℝ (Fin n))
    (hF : ∀ᶠ z in 𝓝 center, HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ᶠ z in 𝓝 center, HasFDerivAt G (H z) z) (hH : ContinuousAt H center)
    (mu : ℝ) (hmu : 0 < mu) (hpositive : ∀ v, mu * ‖v‖ ^ 2 ≤ inner ℝ v (H center v))
    (hconv : Tendsto (fun k => (euclideanPracticalRun P f G x₀ k).point) atTop (𝓝 center))
    (hne : ∀ k, (euclideanPracticalRun P f G x₀ k).point ≠ center)
    (radius : ℝ) (hradius : 0 < radius) :
    ∃ K, ∀ k, K ≤ k → ∀ a ∈ (euclideanPracticalRun P f G x₀ k).pairs, PairNear center radius a := by
  have hinit := euclideanPracticalRun_initial_gradient_ne_zero P f G x₀ center hconv hne
  have hc := algorithmInitialState_constants P hP f G x₀ none hinit
  rcases hP with ⟨_, _, _, _, _, _, hsig, hsig₁, _, _, _, _⟩
  obtain ⟨K, hK⟩ := run_eventually_local_new_pairs P n (euclideanPracticalModel P) f G H
    (algorithmInitialState P f G x₀ none) rfl rfl hc.1 hc.2 hsig (hsig₁.trans (by norm_num))
    center hF hG hH mu hmu hpositive hconv hne radius hradius
  refine ⟨K + (n + 1), ?_⟩
  exact run_finite_forgetting P n (euclideanPracticalModel P) n
    (fun S => ⟨modelDropCount P S, euclideanPracticalModel_pairs_drop P S⟩)
    (fun S => (euclideanPracticalModel_length_le P S).trans (min_le_right _ _)) f G
    (algorithmInitialState P f G x₀ none) (by simp [algorithmInitialState, initialState])
    (PairNear center radius) (fun a u => pairNear_transport center radius a u) K hK

/-- Actual retained images converge relatively to the true limiting
Hessian, uniformly over all stored observations and arbitrarily short
steps. This is derived from genuine observations and local C² data. -/
theorem euclideanPracticalRun_eventually_secant_errors (P : Parameters) (hP : P.Valid n)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (x₀ center : EuclideanSpace ℝ (Fin n))
    (hF : ∀ᶠ z in 𝓝 center, HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ᶠ z in 𝓝 center, HasFDerivAt G (H z) z) (hH : ContinuousAt H center)
    (mu : ℝ) (hmu : 0 < mu) (hpositive : ∀ v, mu * ‖v‖ ^ 2 ≤ inner ℝ v (H center v))
    (hconv : Tendsto (fun k => (euclideanPracticalRun P f G x₀ k).point) atTop (𝓝 center))
    (hne : ∀ k, (euclideanPracticalRun P f G x₀ k).point ≠ center)
    (epsilon : ℝ≥0) (hepsilon : 0 < (epsilon : ℝ)) :
    ∃ K, ∀ k, K ≤ k → ∀ a ∈ (euclideanPracticalRun P f G x₀ k).pairs,
      ‖a.image - H center a.step‖ ≤ (epsilon : ℝ) * ‖a.step‖ := by
  have hclose : ∀ᶠ z in 𝓝 center, ‖H z - H center‖ < (epsilon : ℝ) :=
    (hH.sub continuousAt_const).norm.eventually (gt_mem_nhds (by
      change ‖H center - H center‖ < (epsilon : ℝ)
      rw [sub_self, norm_zero]
      exact hepsilon))
  have hdata : ∀ᶠ z in 𝓝 center, HasFDerivAt G (H z) z ∧ ‖H z - H center‖ ≤ (epsilon : ℝ) := by
    filter_upwards [hG, hclose] with z hg hh
    exact ⟨hg, hh.le⟩
  obtain ⟨radius, hradius, hlocal⟩ := Metric.eventually_nhds_iff.mp hdata
  obtain ⟨K, hK⟩ := euclideanPracticalRun_eventually_local_pairs P hP f G H x₀ center hF hG hH
    mu hmu hpositive hconv hne radius hradius
  refine ⟨K, ?_⟩
  intro k hk a ha
  have hnear := hK k hk a ha
  have hfaithful := euclideanPracticalRun_pairs_faithful P f G x₀ k a ha
  have herr := local_secant_error G H (H center) center radius epsilon
    (fun z hz => (hlocal hz).1) (fun z hz => (hlocal hz).2) a.anchor (a.anchor + a.step)
    (by simpa only [mem_ball, dist_eq_norm] using hnear.1)
    (by simpa only [mem_ball, dist_eq_norm] using hnear.2)
  simpa only [hfaithful.1, add_sub_cancel_left] using herr

end
end krylov.XR
