import krylov.XR.CorrectedSourceGate
import krylov.XR.LocalSelectedQuotient
import krylov.XR.LocalNonempty
import krylov.XR.LocalTrialData

/-!
Article: main_krylov, thm:grow and cor:xrF, selected-model source activation.
Use: original G1--G4 force inactive safeguard and first-unit acceptance
for the literal executor with either value setting. The actual selected
model may be corrected or ordinary; its genuine approximation is proved
from real endpoint data. No successful-test or output field is assumed.
Source: primitive selected-model bounds and the true Taylor quotient.
-/

namespace krylov.XR
noncomputable section
open Set Metric Filter Topology krylov.Methods
open scoped InnerProductSpace NNReal Matrix.Norms.L2Operator
variable {n : ℕ}
set_option maxHeartbeats 800000

/-- Original analytic, incoming-independence, actual trial-adequacy and
fixed-safeguard hypotheses for either setting of the value flag. -/
structure SelectedGrowthSource (P : Parameters)
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
  sourceRadius : ℝ
  sourceRadius_pos : 0 < sourceRadius
  hessianLipschitz : ℝ≥0
  h_lip : LipschitzOnWith hessianLipschitz H (ball center sourceRadius)
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
    0 < M.pairs.length → M.pairs.length < n → algorithmSelectedDirection P S ≠ 0 →
    ell * ‖algorithmSelectedDirection P S‖ ^ 2 ≤ algorithmComputedCurvature P S ∧
      algorithmComputedCurvature P S ≤ trialUpper * ‖algorithmSelectedDirection P S‖ ^ 2 ∧
      inner ℝ (H center (algorithmSelectedDirection P S)) (algorithmSelectedDirection P S) ≤
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

/-- Actual selected-model G1--G4 imply first-unit acceptance and inactive
safeguard, including when function-value correction is enabled. -/
theorem SelectedGrowthSource.first_accepted (D : SelectedGrowthSource P f G H x₀ center bounds)
    (hP : P.Valid n) :
    ∃ K, ∀ k, K ≤ k →
      let S := algorithmRun P f G x₀ bounds k
      (algorithmModel P S).safeDirection S = (algorithmModel P S).direction ∧
        Accepted f P.armijo S.point S.gradient ((algorithmModel P S).safeDirection S) 1 := by
  have hconst := dimension_constants_positive n D.mu D.sigma D.upper D.ell D.trialUpper
    D.mu_pos D.sigma_pos D.upper_pos D.ell_pos
  have harmijo : P.armijo < 1 / 2 := hP.2.2.2.2.2.2.2.1
  let margin : ℝ := min (1 - 2 * P.armijo) D.eta
  have hmargin : 0 < margin := lt_min (by linarith) D.eta_pos
  let C := dimensionQuotientConstant n D.mu D.sigma D.ell
  let epsilon : ℝ := min (dimensionStepRadius n D.mu D.sigma D.upper / 2) (margin / (|C| + 1))
  have he : 0 < epsilon := lt_min (div_pos hconst.1 (by norm_num))
    (div_pos hmargin (by positivity))
  have her : epsilon ≤ dimensionStepRadius n D.mu D.sigma D.upper := by
    have hh := min_le_left (dimensionStepRadius n D.mu D.sigma D.upper / 2) (margin / (|C| + 1))
    change epsilon ≤ _ at hh
    linarith [hconst.1]
  have hallow : C * epsilon ≤ margin := by
    have hb := (le_div_iff₀ (by positivity : 0 < |C| + 1)).mp
      (min_le_right (dimensionStepRadius n D.mu D.sigma D.upper / 2) (margin / (|C| + 1)))
    change epsilon * (|C| + 1) ≤ margin at hb
    nlinarith [mul_le_mul_of_nonneg_right (le_abs_self C) he.le]
  obtain ⟨K₁, hK₁⟩ := algorithmRun_eventually_corrected_data P hP f G H x₀ center bounds
    D.f_deriv D.g_deriv D.h_cont.self_of_nhds D.sourceRadius D.sourceRadius_pos D.hessianLipschitz D.h_lip
    D.mu D.mu_pos D.coercive D.converges D.distinct epsilon he
  obtain ⟨K₂, hK₂⟩ := algorithmRun_eventually_retains_window P hP f G H x₀ center bounds
    D.f_deriv D.g_deriv D.h_cont.self_of_nhds D.mu D.sigma D.mu_pos D.sigma_pos D.coercive
    D.converges D.distinct D.gainStart D.gain
  obtain ⟨K₃, hK₃⟩ := algorithmRun_eventually_incoming_nonempty P hP f G H x₀ center bounds
    D.f_deriv D.g_deriv D.h_cont.self_of_nhds D.mu D.mu_pos D.coercive D.converges D.distinct
  obtain ⟨K₄, hK₄⟩ := algorithmRun_eventually_trial_data P hP f G H x₀ center bounds
    D.f_deriv D.g_deriv D.h_cont D.mu D.mu_pos D.coercive D.converges D.distinct epsilon he
  have hsym := local_hessian_symmetric f G H center D.f_deriv D.g_deriv.self_of_nhds
  refine ⟨max D.gainStart (max D.trialStart (max K₁ (max K₂ (max K₃ K₄)))), ?_⟩
  intro k hk
  let S := algorithmRun P f G x₀ bounds k
  let M := algorithmModel P S
  have hdata := hK₁ k (by omega)
  have hret : M.pairs = incomingWindow S := (hK₂ k (by omega)).2.1
  have hlen : M.pairs.length ≤ n := (algorithmModel_length_le P S).trans (min_le_right _ _)
  have hp : 0 < M.pairs.length := by rw [hret]; exact hK₃ k (by omega)
  have hs (i : Fin M.pairs.length) : storedSteps M.pairs i ≠ 0 :=
    positivePair_step_ne_zero _ (algorithmRun_pairs_positive P f G x₀ bounds k _
      (algorithmModel_pair_mem P S _ (List.get_mem _ i)))
  have hy : ∀ i : Fin M.pairs.length, ‖storedImages M.pairs i - H center (storedSteps M.pairs i)‖ ≤
      epsilon * ‖storedSteps M.pairs i‖ := hdata.1
  have hgain : ∀ w : Fin M.pairs.length → ℝ, D.sigma ^ 2 * ‖WithLp.toLp 2 w‖ ^ 2 ≤
      ‖combine (krylov.Convergence.unitWindow (storedSteps M.pairs)) w‖ ^ 2 := by
    rw [hret]
    exact D.gain k (by omega)
  have hmodel := selectedModel_normalized_error P (H center) hsym M.pairs hs epsilon he.le hy hdata.2.2
  have hsmall := (localStepRadius_small D.mu D.sigma D.upper epsilon D.mu_pos D.sigma_pos D.upper_pos he.le
    (her.trans (prefixMinimum_le _ n M.pairs.length hlen))).2.1
  have hdom := local_raw_window_domains (H center) hsym (storedSteps M.pairs) (storedImages M.pairs) hs
    D.mu D.sigma epsilon D.mu_pos D.sigma_pos he.le D.coercive hgain hy hsmall
  have ht := fun hd => D.trial k (by omega) hp (algorithmModel_selected_partial P S hdom.2.2.1 hd) hd
  have htrial := fun hd => And.intro (ht hd).1 (ht hd).2.1
  have hrelated := algorithmModel_selected_gradientRelated P S hp.ne' (H center) hsym
    D.mu D.sigma D.upper D.ell D.trialUpper epsilon D.mu_pos D.sigma_pos D.upper_pos D.ell_pos
    D.trialUpper_pos he.le her D.coercive D.h_norm hs hgain hy hmodel htrial
  have hc := run_cache_constants P n (algorithmModel P) f G
    (algorithmInitialState P f G x₀ bounds) rfl rfl k
  have hinactive : M.safeDirection S = M.direction :=
    safeguard_eq_of_stronger_bounds S.descentConstant S.normConstant
      (dimensionDescentConstant n D.mu D.sigma D.upper D.trialUpper)
      (dimensionNormConstant n D.mu D.sigma D.upper D.ell) M.fallbackCurvature S.gradient M.direction hrelated
      (by rw [show S.descentConstant = _ from hc.2.2.1]; exact D.safeguard_descent.le)
      (by rw [show S.normConstant = _ from hc.2.2.2]; exact D.safeguard_norm.le)
  have hTaylor := hK₄ k (by omega)
  dsimp only at hTaylor ⊢
  change M.safeDirection S = M.direction ∧ Accepted f P.armijo S.point S.gradient (M.safeDirection S) 1
  change S.gradient ≠ 0 ∧ _ at hTaylor
  rw [hinactive] at hTaylor
  have hq := algorithmModel_selected_quotient P S hp.ne' f G H (H center) hsym
    D.mu D.sigma D.upper D.ell D.trialUpper epsilon D.mu_pos D.sigma_pos D.upper_pos D.ell_pos
    D.trialUpper_pos he.le her D.coercive D.h_norm hs hgain hy hmodel hTaylor.1 hc.2.1.symm htrial
    hTaylor.2.1 hTaylor.2.2.1 hTaylor.2.2.2.1 hTaylor.2.2.2.2
  refine ⟨hinactive, ?_⟩
  rw [hinactive]
  exact quotient_acceptance_from_margin (H center) (algorithmSelectedDirection P S)
    _ (algorithmComputedCurvature P S) C epsilon P.armijo D.eta D.ell D.ell_pos
    (by
      dsimp only at hq
      split_ifs with hd
      · simpa only [hd, ite_true] using hq
      · simpa only [hd, ite_false] using hq)
    (fun hd => ⟨(ht hd).1, (ht hd).2.2⟩) hallow

end
end krylov.XR
