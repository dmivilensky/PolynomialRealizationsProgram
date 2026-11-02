import krylov.XR.GrowthRitz
import krylov.XR.LocalProbeMemory

/-!
Article: main_krylov, thm:XR, source-derived bounded running Ritz estimates.
Use: prove the upper bound for the real first and rejected-probe ModelSteps
from original G1--G2. No bounded-Ritz, accepted-query or model-error premise
is a source field. Source: genuine finite-memory localization, normalized
Rayleigh perturbation and the actual max update.
-/
namespace krylov.XR
noncomputable section
open Matrix Set Metric Filter Topology krylov.Methods
open scoped InnerProductSpace NNReal
variable {n : ℕ}
set_option maxHeartbeats 800000

/-- Primitive real observed-window data bound the actual Ritz contribution. -/
theorem modelRitzBound_of_observations (P : Parameters) (hinfl : 0 ≤ P.inflation)
    (S : State (EuclideanSpace ℝ (Fin n)))
    (H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hH : H.toLinearMap.IsSymmetric) (mu upper sigma epsilon : ℝ)
    (hsigma : 0 < sigma) (he : 0 ≤ epsilon)
    (hpositive : ∀ v, mu * ‖v‖ ^ 2 ≤ inner ℝ v (H v)) (hnorm : ‖H‖ ≤ upper)
    (hsteps : ∀ a ∈ S.pairs, positivePair a)
    (hgain : ∀ w : Fin (algorithmModel P S).pairs.length → ℝ,
      sigma ^ 2 * ‖WithLp.toLp 2 w‖ ^ 2 ≤
        ‖combine (krylov.Convergence.unitWindow (storedSteps (algorithmModel P S).pairs)) w‖ ^ 2)
    (hy : ∀ a ∈ S.pairs, ‖a.image - H a.step‖ ≤ epsilon * ‖a.step‖) :
    ModelRitzBound P (P.inflation * (upper + (n : ℝ) * epsilon / sigma ^ 2)) S := by
  intro hlen
  let W := (algorithmModel P S).pairs
  have hs (i : Fin W.length) : storedSteps W i ≠ 0 := by
    have hp := hsteps (W.get i) (algorithmModel_pair_mem P S _ (List.get_mem _ i))
    intro hz
    change storedSteps W i = 0 at hz
    change 0 < inner ℝ (storedSteps W i) (storedImages W i) at hp
    rw [hz, inner_zero_left] at hp
    exact hp.false
  have herr (i : Fin W.length) : ‖storedImages W i - H (storedSteps W i)‖ ≤
      epsilon * ‖storedSteps W i‖ := hy _ (algorithmModel_pair_mem P S _ (List.get_mem _ i))
  have hh := observedRitz_sup_le H hH W hlen hs mu upper sigma epsilon hsigma he
    hpositive hnorm hgain herr
  have hcard : (W.length : ℝ) ≤ n := by
    exact_mod_cast (algorithmModel_length_le P S).trans (min_le_right _ _)
  apply (mul_le_mul_of_nonneg_left hh hinfl).trans
  apply mul_le_mul_of_nonneg_left _ hinfl
  have hdelta := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right hcard he) (sq_nonneg sigma)
  linarith

/-- Under original G1--G2, every actually visited first or second
ModelStep has a single source-derived uniform Ritz upper bound. -/
theorem algorithmRun_eventually_modelRitzBound (P : Parameters) (hP : P.Valid n)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (x₀ center : EuclideanSpace ℝ (Fin n)) (bounds : SpectralBounds)
    (hF : ∀ᶠ z in 𝓝 center, HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ᶠ z in 𝓝 center, HasFDerivAt G (H z) z) (hH : ContinuousAt H center)
    (mu sigma : ℝ) (hmu : 0 < mu) (hsigma : 0 < sigma)
    (hpositive : ∀ v, mu * ‖v‖ ^ 2 ≤ inner ℝ v (H center v))
    (hconv : Tendsto (fun k => (algorithmRun P f G x₀ bounds k).point) atTop (𝓝 center))
    (hne : ∀ k, (algorithmRun P f G x₀ bounds k).point ≠ center)
    (K₀ : ℕ)
    (hgain : ∀ k, K₀ ≤ k →
      let W := incomingWindow (algorithmRun P f G x₀ bounds k)
      ∀ w : Fin W.length → ℝ, sigma ^ 2 * ‖WithLp.toLp 2 w‖ ^ 2 ≤
        ‖combine (krylov.Convergence.unitWindow (storedSteps W)) w‖ ^ 2)
    (hprobeGain : ∀ k, K₀ ≤ k →
      let S := algorithmRun P f G x₀ bounds k
      ¬Accepted f P.armijo S.point S.gradient ((algorithmModel P S).safeDirection S) 1 →
      let W := incomingWindow (firstProbeState (algorithmModel P) f G S)
      ∀ w : Fin W.length → ℝ, sigma ^ 2 * ‖WithLp.toLp 2 w‖ ^ 2 ≤
        ‖combine (krylov.Convergence.unitWindow (storedSteps W)) w‖ ^ 2) :
    ∃ C > 0, ∃ K, ∀ k, K ≤ k →
      let S := algorithmRun P f G x₀ bounds k
      ModelRitzBound P C S ∧
        (¬Accepted f P.armijo S.point S.gradient ((algorithmModel P S).safeDirection S) 1 →
          ModelRitzBound P C (firstProbeState (algorithmModel P) f G S)) := by
  let upper := ‖H center‖ + 1
  let C := P.inflation * (upper + (n : ℝ) / sigma ^ 2)
  have hinfl : 0 < P.inflation := lt_trans (by norm_num) hP.2.2.2.2.1
  have hC : 0 < C := by dsimp only [C, upper]; positivity
  have hsym := local_hessian_symmetric f G H center hF hG.self_of_nhds
  obtain ⟨Kr, hr⟩ := algorithmRun_eventually_retains_window P hP f G H x₀ center bounds
    hF hG hH mu sigma hmu hsigma hpositive hconv hne K₀ hgain
  obtain ⟨Kp, hp⟩ := algorithmRun_eventually_probe_retains_window P hP f G H x₀ center bounds
    hF hG hH mu sigma hmu hsigma hpositive hconv hne K₀ hprobeGain
  obtain ⟨Ke, he⟩ := algorithmRun_eventually_secant_errors P hP f G H x₀ center bounds
    hF hG hH mu hmu hpositive hconv hne 1 (by norm_num)
  obtain ⟨Kq, hq⟩ := algorithmRun_eventually_probe_secant_errors P hP f G H x₀ center bounds
    hF hG hH mu hmu hpositive hconv hne 1 (by norm_num)
  refine ⟨C, hC, max K₀ (max Kr (max Kp (max Ke Kq))), ?_⟩
  intro k hk
  let S := algorithmRun P f G x₀ bounds k
  have hnorm : ‖H center‖ ≤ upper := by dsimp only [upper]; linarith
  have hf : ModelRitzBound P C S := by
    have hret := (hr k (by omega)).2.1
    have hg := hgain k (by omega)
    dsimp only at hg hret
    rw [←hret] at hg
    simpa only [mul_one, NNReal.coe_one] using
      modelRitzBound_of_observations P hinfl.le S (H center) hsym mu upper sigma 1 hsigma
        (by norm_num) hpositive hnorm (algorithmRun_pairs_positive P f G x₀ bounds k) hg
        (he k (by omega))
  refine ⟨hf, ?_⟩
  intro hreject
  have hret := (hp k (by omega) hreject).2.1
  have hg := hprobeGain k (by omega) hreject
  dsimp only at hg hret
  change ∀ w : Fin (incomingWindow (firstProbeState (algorithmModel P) f G S)).length → ℝ,
    sigma ^ 2 * ‖WithLp.toLp 2 w‖ ^ 2 ≤
      ‖combine (krylov.Convergence.unitWindow
        (storedSteps (incomingWindow (firstProbeState (algorithmModel P) f G S)))) w‖ ^ 2 at hg
  rw [←hret] at hg
  simpa only [mul_one, NNReal.coe_one] using
    modelRitzBound_of_observations P hinfl.le (firstProbeState (algorithmModel P) f G S)
      (H center) hsym mu upper sigma 1 hsigma (by norm_num) hpositive hnorm
      (firstProbeState_positive P f G S (algorithmRun_pairs_positive P f G x₀ bounds k))
      hg (hq k (by omega))

/-- The actual running upper estimates stay bounded under G1--G2 alone,
including all real rejected-probe model updates. -/
theorem algorithmRun_source_running_upper_bounded (P : Parameters) (hP : P.Valid n)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (x₀ center : EuclideanSpace ℝ (Fin n)) (bounds : SpectralBounds)
    (hF : ∀ᶠ z in 𝓝 center, HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ᶠ z in 𝓝 center, HasFDerivAt G (H z) z) (hH : ContinuousAt H center)
    (mu sigma : ℝ) (hmu : 0 < mu) (hsigma : 0 < sigma)
    (hpositive : ∀ v, mu * ‖v‖ ^ 2 ≤ inner ℝ v (H center v))
    (hconv : Tendsto (fun k => (algorithmRun P f G x₀ bounds k).point) atTop (𝓝 center))
    (hne : ∀ k, (algorithmRun P f G x₀ bounds k).point ≠ center)
    (K₀ : ℕ)
    (hgain : ∀ k, K₀ ≤ k →
      let W := incomingWindow (algorithmRun P f G x₀ bounds k)
      ∀ w : Fin W.length → ℝ, sigma ^ 2 * ‖WithLp.toLp 2 w‖ ^ 2 ≤
        ‖combine (krylov.Convergence.unitWindow (storedSteps W)) w‖ ^ 2)
    (hprobeGain : ∀ k, K₀ ≤ k →
      let S := algorithmRun P f G x₀ bounds k
      ¬Accepted f P.armijo S.point S.gradient ((algorithmModel P S).safeDirection S) 1 →
      let W := incomingWindow (firstProbeState (algorithmModel P) f G S)
      ∀ w : Fin W.length → ℝ, sigma ^ 2 * ‖WithLp.toLp 2 w‖ ^ 2 ≤
        ‖combine (krylov.Convergence.unitWindow (storedSteps W)) w‖ ^ 2) :
    ∃ C > 0, ∃ K, ∀ k, K ≤ k → boundsUpper (algorithmRun P f G x₀ bounds k).bounds ≤ C := by
  obtain ⟨C, hC, K, hK⟩ := algorithmRun_eventually_modelRitzBound P hP f G H x₀ center bounds
    hF hG hH mu sigma hmu hsigma hpositive hconv hne K₀ hgain hprobeGain
  refine ⟨max (boundsUpper (algorithmRun P f G x₀ bounds K).bounds) C,
    lt_of_lt_of_le hC (le_max_right _ _), K, ?_⟩
  exact algorithmRun_boundsUpper_bounded P C hC.le f G x₀ bounds K hK

end
end krylov.XR
