import krylov.XR.EuclideanSourceGate
import krylov.XR.EuclideanLocalQuotient
import krylov.XR.EuclideanNonempty
import krylov.XR.EuclideanTrialData

/-!
Article: main_krylov, thm:grow and cor:xrF, selected-model source activation.
Use: original G1--G4 force inactive safeguard and first-unit acceptance
for the literal Euclidean-split executor with either value setting. The actual selected
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
fixed-safeguard hypotheses for the literal Euclidean-split value option. -/
structure EuclideanGrowthSource (P : Parameters)
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
  converges : Tendsto (fun k => (euclideanAlgorithmRun P f G x₀ bounds k).point) atTop (𝓝 center)
  distinct : ∀ k, (euclideanAlgorithmRun P f G x₀ bounds k).point ≠ center
  gainStart : ℕ
  gain : ∀ k, gainStart ≤ k →
    let W := incomingWindow (euclideanAlgorithmRun P f G x₀ bounds k)
    ∀ w : Fin W.length → ℝ, sigma ^ 2 * ‖WithLp.toLp 2 w‖ ^ 2 ≤
      ‖combine (krylov.Convergence.unitWindow (storedSteps W)) w‖ ^ 2
  trialStart : ℕ
  trial : ∀ k, trialStart ≤ k →
    let S := euclideanAlgorithmRun P f G x₀ bounds k
    let M := euclideanAlgorithmModel P S
    0 < M.pairs.length → M.pairs.length < n → euclideanSelectedDirection P S ≠ 0 →
    ell * ‖euclideanSelectedDirection P S‖ ^ 2 ≤ euclideanComputedCurvature P S ∧
      euclideanComputedCurvature P S ≤ trialUpper * ‖euclideanSelectedDirection P S‖ ^ 2 ∧
      inner ℝ (H center (euclideanSelectedDirection P S)) (euclideanSelectedDirection P S) ≤
        (2 * (1 - P.armijo) - eta) * euclideanComputedCurvature P S
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
theorem EuclideanGrowthSource.first_accepted (D : EuclideanGrowthSource P f G H x₀ center bounds)
    (hP : P.Valid n) :
    ∃ K, ∀ k, K ≤ k →
      let S := euclideanAlgorithmRun P f G x₀ bounds k
      (euclideanAlgorithmModel P S).safeDirection S = (euclideanAlgorithmModel P S).direction ∧
        Accepted f P.armijo S.point S.gradient ((euclideanAlgorithmModel P S).safeDirection S) 1 := by
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
  obtain ⟨K₁, hK₁⟩ := euclideanAlgorithmRun_eventually_corrected_data P hP f G H x₀ center bounds
    D.f_deriv D.g_deriv D.h_cont.self_of_nhds D.sourceRadius D.sourceRadius_pos D.hessianLipschitz D.h_lip
    D.mu D.mu_pos D.coercive D.converges D.distinct epsilon he
  obtain ⟨K₂, hK₂⟩ := euclideanAlgorithmRun_eventually_retains_window P hP f G H x₀ center bounds
    D.f_deriv D.g_deriv D.h_cont.self_of_nhds D.mu D.sigma D.mu_pos D.sigma_pos D.coercive
    D.converges D.distinct D.gainStart D.gain
  obtain ⟨K₃, hK₃⟩ := euclideanAlgorithmRun_eventually_incoming_nonempty P hP f G H x₀ center bounds
    D.f_deriv D.g_deriv D.h_cont.self_of_nhds D.mu D.mu_pos D.coercive D.converges D.distinct
  obtain ⟨K₄, hK₄⟩ := euclideanAlgorithmRun_eventually_trial_data P hP f G H x₀ center bounds
    D.f_deriv D.g_deriv D.h_cont D.mu D.mu_pos D.coercive D.converges D.distinct epsilon he
  have hsym := local_hessian_symmetric f G H center D.f_deriv D.g_deriv.self_of_nhds
  refine ⟨max D.gainStart (max D.trialStart (max K₁ (max K₂ (max K₃ K₄)))), ?_⟩
  intro k hk
  let S := euclideanAlgorithmRun P f G x₀ bounds k
  let M := euclideanAlgorithmModel P S
  have hdata := hK₁ k (by omega)
  have hret : M.pairs = incomingWindow S := (hK₂ k (by omega)).2.1
  have hlen : M.pairs.length ≤ n := (euclideanAlgorithmModel_length_le P S).trans (min_le_right _ _)
  have hp : 0 < M.pairs.length := by rw [hret]; exact hK₃ k (by omega)
  have hs (i : Fin M.pairs.length) : storedSteps M.pairs i ≠ 0 :=
    positivePair_step_ne_zero _ (euclideanAlgorithmRun_pairs_positive P f G x₀ bounds k _
      (euclideanAlgorithmModel_pair_mem P S _ (List.get_mem _ i)))
  have hy : ∀ i : Fin M.pairs.length, ‖storedImages M.pairs i - H center (storedSteps M.pairs i)‖ ≤
      epsilon * ‖storedSteps M.pairs i‖ := hdata.1
  have hgain : ∀ w : Fin M.pairs.length → ℝ, D.sigma ^ 2 * ‖WithLp.toLp 2 w‖ ^ 2 ≤
      ‖combine (krylov.Convergence.unitWindow (storedSteps M.pairs)) w‖ ^ 2 := by
    rw [hret]
    exact D.gain k (by omega)
  have hmodel := selectedEuclideanModel_normalized_error P S.point (H center) hsym M.pairs hs epsilon he.le hy hdata.2.2
  have hsmall := (localStepRadius_small D.mu D.sigma D.upper epsilon D.mu_pos D.sigma_pos D.upper_pos he.le
    (her.trans (prefixMinimum_le _ n M.pairs.length hlen))).2.1
  have hdom := local_raw_window_domains (H center) hsym (storedSteps M.pairs) (storedImages M.pairs) hs
    D.mu D.sigma epsilon D.mu_pos D.sigma_pos he.le D.coercive hgain hy hsmall
  have ht := fun hd => D.trial k (by omega) hp (euclideanAlgorithmModel_selected_partial P S hdom.2.2.1 hd) hd
  have htrial := fun hd => And.intro (ht hd).1 (ht hd).2.1
  have hrelated := euclideanAlgorithmModel_selected_gradientRelated P S hp.ne' (H center) hsym
    D.mu D.sigma D.upper D.ell D.trialUpper epsilon D.mu_pos D.sigma_pos D.upper_pos D.ell_pos
    D.trialUpper_pos he.le her D.coercive D.h_norm hs hgain hy hmodel htrial
  have hc := run_cache_constants P n (euclideanAlgorithmModel P) f G
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
  have hq := euclideanAlgorithmModel_selected_quotient P S hp.ne' f G H (H center) hsym
    D.mu D.sigma D.upper D.ell D.trialUpper epsilon D.mu_pos D.sigma_pos D.upper_pos D.ell_pos
    D.trialUpper_pos he.le her D.coercive D.h_norm hs hgain hy hmodel hTaylor.1 hc.2.1.symm htrial
    hTaylor.2.1 hTaylor.2.2.1 hTaylor.2.2.2.1 hTaylor.2.2.2.2
  refine ⟨hinactive, ?_⟩
  rw [hinactive]
  exact quotient_acceptance_from_margin (H center) (euclideanSelectedDirection P S)
    _ (euclideanComputedCurvature P S) C epsilon P.armijo D.eta D.ell D.ell_pos
    (by
      dsimp only at hq
      split_ifs with hd
      · simpa only [hd, ite_true] using hq
      · simpa only [hd, ite_false] using hq)
    (fun hd => ⟨(ht hd).1, (ht hd).2.2⟩) hallow

/-- All observable activation conclusions hold together on one actual tail.
The source assumptions are precisely the analytic and pre-cleanup G1--G4
conditions above; no successful deletion, safeguard or search test is assumed. -/
theorem EuclideanGrowthSource.activation (D : EuclideanGrowthSource P f G H x₀ center bounds)
    (hP : P.Valid n) :
    ∃ K, ∀ k, K ≤ k →
      let S := euclideanAlgorithmRun P f G x₀ bounds k
      rankDeletion (incomingWindow S) = 0 ∧
        (euclideanAlgorithmModel P S).pairs = incomingWindow S ∧
        (euclideanAlgorithmModel P S).pairsBeforeTest = (incomingWindow S).length ∧
        (euclideanAlgorithmModel P S).deletedByTest = 0 ∧
        (euclideanAlgorithmModel P S).safeDirection S = (euclideanAlgorithmModel P S).direction ∧
        Accepted f P.armijo S.point S.gradient ((euclideanAlgorithmModel P S).safeDirection S) 1 := by
  obtain ⟨K₁, hK₁⟩ := euclideanAlgorithmRun_eventually_retains_window P hP f G H x₀ center bounds
    D.f_deriv D.g_deriv D.h_cont.self_of_nhds D.mu D.sigma D.mu_pos D.sigma_pos D.coercive
    D.converges D.distinct D.gainStart D.gain
  obtain ⟨K₂, hK₂⟩ := D.first_accepted hP
  refine ⟨max K₁ K₂, ?_⟩
  intro k hk
  exact ⟨(hK₁ k (by omega)).1, (hK₁ k (by omega)).2.1,
    (hK₁ k (by omega)).2.2.1, (hK₁ k (by omega)).2.2.2,
    (hK₂ k (by omega)).1, (hK₂ k (by omega)).2⟩

/-- With values enabled, the actually computed Euclidean correction and
both real value gates are eventually selected on the literal run. -/
theorem EuclideanGrowthSource.corrected_selection (D : EuclideanGrowthSource P f G H x₀ center bounds)
    (hP : P.Valid n) (hon : P.valuesEnabled = true) :
    ∃ K, ∀ k, K ≤ k →
      let S := euclideanAlgorithmRun P f G x₀ bounds k
      let W := (euclideanAlgorithmModel P S).pairs
      (∀ i : Fin W.length, |12 * euclideanStoredSplit S.point W i * (W.get i).valueDefect| ≤
        storedPairing W i i / 2) ∧
        euclideanCorrectedWindowPasses P.windowThreshold S.point W ∧
        selectedEuclideanModel P S.point W = euclideanStoredValueModel S.point W :=
  euclideanAlgorithmRun_eventually_corrected_gates P hP hon f G H x₀ center bounds
    D.f_deriv D.g_deriv D.h_cont.self_of_nhds D.sourceRadius D.sourceRadius_pos D.hessianLipschitz D.h_lip
    D.mu D.sigma D.mu_pos D.sigma_pos D.coercive D.converges D.distinct D.gainStart D.gain

end
end krylov.XR
