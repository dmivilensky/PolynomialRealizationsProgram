import krylov.XR.LocalNewPairs
import krylov.XR.MemoryFiniteForgetting

/-!
Article: main_krylov, G1 and proof of thm:grow, actual local-window bootstrap.
Use: derive locality and arbitrarily small actual relative secant errors
for every retained observation directly from the original local C² source
and accepted convergence. Old data are removed by the real n+1-step
forgetting theorem; no localization or model-convergence field is assumed.
Source: true local stationarity, safeguard query bounds and suffix memory.
-/

namespace krylov.XR
noncomputable section
open Set Metric Filter Topology
open scoped InnerProductSpace NNReal
variable {n : ℕ}

/-- A nonstationary accepted trajectory converging to its distinct limit
cannot have started with a zero gradient in the literal stopped executor. -/
theorem algorithmRun_initial_gradient_ne_zero (P : Parameters)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (x₀ center : EuclideanSpace ℝ (Fin n)) (bounds : SpectralBounds)
    (hconv : Tendsto (fun k => (algorithmRun P f G x₀ bounds k).point) atTop (𝓝 center))
    (hne : ∀ k, (algorithmRun P f G x₀ bounds k).point ≠ center) : G x₀ ≠ 0 := by
  intro hzero
  have hr k : algorithmRun P f G x₀ bounds k = algorithmInitialState P f G x₀ bounds :=
    run_stationary P n (algorithmModel P) f G _ hzero k
  have hconst : Tendsto (fun k => (algorithmRun P f G x₀ bounds k).point) atTop (𝓝 x₀) := by
    simpa only [hr, algorithmInitialState, initialState] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => x₀) atTop (𝓝 x₀))
  have heq : x₀ = center := tendsto_nhds_unique hconst hconv
  exact hne 0 heq

/-- Every genuine stored segment of literal XR is eventually contained
in any prescribed neighbourhood of the accepted nondegenerate limit. -/
theorem algorithmRun_eventually_local_pairs (P : Parameters) (hP : P.Valid n)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (x₀ center : EuclideanSpace ℝ (Fin n)) (bounds : SpectralBounds)
    (hF : ∀ᶠ z in 𝓝 center, HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ᶠ z in 𝓝 center, HasFDerivAt G (H z) z) (hH : ContinuousAt H center)
    (mu : ℝ) (hmu : 0 < mu) (hpositive : ∀ v, mu * ‖v‖ ^ 2 ≤ inner ℝ v (H center v))
    (hconv : Tendsto (fun k => (algorithmRun P f G x₀ bounds k).point) atTop (𝓝 center))
    (hne : ∀ k, (algorithmRun P f G x₀ bounds k).point ≠ center)
    (radius : ℝ) (hradius : 0 < radius) :
    ∃ K, ∀ k, K ≤ k → ∀ a ∈ (algorithmRun P f G x₀ bounds k).pairs, PairNear center radius a := by
  have hinit := algorithmRun_initial_gradient_ne_zero P f G x₀ center bounds hconv hne
  have hc := algorithmInitialState_constants P hP f G x₀ bounds hinit
  rcases hP with ⟨_, _, _, _, _, _, hsig, hsig₁, _, _, _, _⟩
  obtain ⟨K, hK⟩ := run_eventually_local_new_pairs P n (algorithmModel P) f G H
    (algorithmInitialState P f G x₀ bounds) rfl rfl hc.1 hc.2 hsig (hsig₁.trans (by norm_num))
    center hF hG hH mu hmu hpositive hconv hne radius hradius
  refine ⟨K + (n + 1), ?_⟩
  exact run_finite_forgetting P n (algorithmModel P) n
    (fun S => ⟨modelDropCount P S, algorithmModel_pairs_drop P S⟩)
    (fun S => (algorithmModel_length_le P S).trans (min_le_right _ _)) f G
    (algorithmInitialState P f G x₀ bounds) (by simp [algorithmInitialState, initialState])
    (PairNear center radius) (fun a u => pairNear_transport center radius a u) K hK

/-- Actual retained images converge relatively to the true limiting
Hessian, uniformly over all stored observations and arbitrarily short
steps. This is derived from genuine observations and local C² data. -/
theorem algorithmRun_eventually_secant_errors (P : Parameters) (hP : P.Valid n)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (x₀ center : EuclideanSpace ℝ (Fin n)) (bounds : SpectralBounds)
    (hF : ∀ᶠ z in 𝓝 center, HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ᶠ z in 𝓝 center, HasFDerivAt G (H z) z) (hH : ContinuousAt H center)
    (mu : ℝ) (hmu : 0 < mu) (hpositive : ∀ v, mu * ‖v‖ ^ 2 ≤ inner ℝ v (H center v))
    (hconv : Tendsto (fun k => (algorithmRun P f G x₀ bounds k).point) atTop (𝓝 center))
    (hne : ∀ k, (algorithmRun P f G x₀ bounds k).point ≠ center)
    (epsilon : ℝ≥0) (hepsilon : 0 < (epsilon : ℝ)) :
    ∃ K, ∀ k, K ≤ k → ∀ a ∈ (algorithmRun P f G x₀ bounds k).pairs,
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
  obtain ⟨K, hK⟩ := algorithmRun_eventually_local_pairs P hP f G H x₀ center bounds hF hG hH
    mu hmu hpositive hconv hne radius hradius
  refine ⟨K, ?_⟩
  intro k hk a ha
  have hnear := hK k hk a ha
  have hfaithful := algorithmRun_pairs_faithful P f G x₀ bounds k a ha
  have herr := local_secant_error G H (H center) center radius epsilon
    (fun z hz => (hlocal hz).1) (fun z hz => (hlocal hz).2) a.anchor (a.anchor + a.step)
    (by simpa only [mem_ball, dist_eq_norm] using hnear.1)
    (by simpa only [mem_ball, dist_eq_norm] using hnear.2)
  simpa only [hfaithful.1, add_sub_cancel_left] using herr

end
end krylov.XR
