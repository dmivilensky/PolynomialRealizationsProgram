import krylov.XR.LocalLimitStationary
import krylov.XR.ExecutionQueryBounds
import krylov.XR.GlobalAlgorithm
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
Article: main_krylov, G1 and thm:grow, actual local criticality bridge.
Use: instantiate the local accepted-limit argument on the literal XR run,
deriving its local Lipschitz gradient from genuine continuous Hessians.
Only local first/second derivatives and accepted convergence are assumed;
the stationary-initial branch is included. Source: the derivative mean
value theorem and the genuine local Armijo/backtracking proof.
-/

namespace krylov.XR
noncomputable section
open Set Metric Filter Topology
open scoped InnerProductSpace NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The true limiting Hessian is symmetric by Schwarz, rather than a
symmetry certificate postulated for the observed local source. -/
theorem local_hessian_symmetric (f : E → ℝ) (G : E → E) (H : E → E →L[ℝ] E)
    (center : E) (hF : ∀ᶠ z in 𝓝 center, HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : HasFDerivAt G (H center) center) : (H center).toLinearMap.IsSymmetric := by
  have hDG : HasFDerivAt (fun z => innerSL ℝ (G z)) ((innerSL ℝ).comp (H center)) center :=
    (innerSL ℝ).hasFDerivAt.comp center hG
  intro a b
  have hs := second_derivative_symmetric_of_eventually hF hDG a b
  change inner ℝ (H center a) b = inner ℝ (H center b) a at hs
  exact hs.trans (real_inner_comm _ _)

/-- Genuine C² data near the limit produce the local-ball first-derivative
and positive Lipschitz constants needed by the actual executor proof. -/
theorem exists_local_gradient_data (f : E → ℝ) (G : E → E) (H : E → E →L[ℝ] E)
    (center : E) (hF : ∀ᶠ z in 𝓝 center, HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ᶠ z in 𝓝 center, HasFDerivAt G (H z) z) (hH : ContinuousAt H center) :
    ∃ radius : ℝ, 0 < radius ∧ ∃ L : ℝ≥0, 0 < (L : ℝ) ∧
      (∀ z ∈ ball center radius, HasFDerivAt f (innerSL ℝ (G z)) z) ∧
        LipschitzOnWith L G (ball center radius) := by
  let L : ℝ≥0 := ⟨‖H center‖ + 1, by positivity⟩
  have hbound : ∀ᶠ z in 𝓝 center, ‖H z‖ < (L : ℝ) :=
    hH.norm.eventually (gt_mem_nhds (by change ‖H center‖ < ‖H center‖ + 1; linarith))
  have hall : ∀ᶠ z in 𝓝 center, HasFDerivAt f (innerSL ℝ (G z)) z ∧
      HasFDerivAt G (H z) z ∧ ‖H z‖ ≤ (L : ℝ) := by
    filter_upwards [hF, hG, hbound] with z hf hg hh
    exact ⟨hf, hg, hh.le⟩
  obtain ⟨radius, hradius, hdata⟩ := Metric.eventually_nhds_iff.mp hall
  refine ⟨radius, hradius, L, by change 0 < ‖H center‖ + 1; positivity,
    fun z hz => (hdata hz).1, ?_⟩
  exact gradient_lipschitzOn_of_hessian_norm G H center radius L
    (fun z hz => (hdata hz).2.1) (fun z hz => (hdata hz).2.2)

/-- The actual accepted limit of literal XR is critical under the
original local C² hypothesis, with no added global regularity assumption. -/
theorem algorithmRun_local_limit_stationary {n : ℕ} (P : Parameters) (hP : P.Valid n)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (x₀ center : EuclideanSpace ℝ (Fin n)) (bounds : SpectralBounds)
    (hF : ∀ᶠ z in 𝓝 center, HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ᶠ z in 𝓝 center, HasFDerivAt G (H z) z) (hH : ContinuousAt H center)
    (hconv : Tendsto (fun k => (algorithmRun P f G x₀ bounds k).point) atTop (𝓝 center)) :
    G center = 0 := by
  by_cases hzero : G x₀ = 0
  · have hr k : algorithmRun P f G x₀ bounds k = algorithmInitialState P f G x₀ bounds :=
      run_stationary P n (algorithmModel P) f G _ hzero k
    have hconst : Tendsto (fun k => (algorithmRun P f G x₀ bounds k).point) atTop (𝓝 x₀) := by
      simpa only [hr, algorithmInitialState, initialState] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => x₀) atTop (𝓝 x₀))
    have heq : x₀ = center := tendsto_nhds_unique hconst hconv
    rw [← heq]
    exact hzero
  · obtain ⟨radius, hradius, L, hL, hf, hg⟩ := exists_local_gradient_data f G H center hF hG hH
    have hc := algorithmInitialState_constants P hP f G x₀ bounds hzero
    rcases hP with ⟨_, _, _, _, _, _, hsig, hsig₁, _, _, _, _⟩
    exact run_local_limit_stationary P n (algorithmModel P) f G
      (algorithmInitialState P f G x₀ bounds) rfl rfl hc.1 hc.2 hsig (hsig₁.trans (by norm_num))
      center radius hradius hf L hL hg hconv

end
end krylov.XR
