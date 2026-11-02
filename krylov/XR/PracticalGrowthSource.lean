import krylov.XR.PracticalGrowthValues
import krylov.XR.CapacityGrowth

/-!
# Practical XR: source assumptions to literal memory growth

Article Theorem 7.3 (`thm:grow`) and Corollary 7.4 (`cor:xrF`). This source
contains only local derivative data, convergence, incoming independence,
partial-window trial adequacy and fixed safeguard inequalities. Retention,
unit acceptance and the entire capacity transition are conclusions.
-/
namespace krylov.XR
noncomputable section
open Set Metric Filter Topology krylov.Methods
open scoped InnerProductSpace NNReal Matrix.Norms.L2Operator
variable {n : ℕ}
set_option maxHeartbeats 800000

/-- Original analytic, incoming-independence, actual trial-adequacy and
fixed-safeguard hypotheses for either setting of the value flag. -/
structure PracticalGrowthSource (P : Parameters)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (x₀ center : EuclideanSpace ℝ (Fin n)) where
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
  converges : Tendsto (fun k => (practicalRun P f G x₀ k).point) atTop (𝓝 center)
  distinct : ∀ k, (practicalRun P f G x₀ k).point ≠ center
  gainStart : ℕ
  gain : ∀ k, gainStart ≤ k →
    let W := incomingWindow (practicalRun P f G x₀ k)
    ∀ w : Fin W.length → ℝ, sigma ^ 2 * ‖WithLp.toLp 2 w‖ ^ 2 ≤
      ‖combine (krylov.Convergence.unitWindow (storedSteps W)) w‖ ^ 2
  trialStart : ℕ
  trial : ∀ k, trialStart ≤ k →
    let S := practicalRun P f G x₀ k
    let M := practicalModel P S
    0 < M.pairs.length → M.pairs.length < n → practicalSelectedDirection P S ≠ 0 →
    ell * ‖practicalSelectedDirection P S‖ ^ 2 ≤ practicalComputedCurvature P S ∧
      practicalComputedCurvature P S ≤ trialUpper * ‖practicalSelectedDirection P S‖ ^ 2 ∧
      inner ℝ (H center (practicalSelectedDirection P S)) (practicalSelectedDirection P S) ≤
        (2 * (1 - P.armijo) - eta) * practicalComputedCurvature P S
  safeguard_descent : (algorithmInitialState P f G x₀ none).descentConstant <
    dimensionDescentConstant n mu sigma upper trialUpper
  safeguard_norm : dimensionNormConstant n mu sigma upper ell <
    (algorithmInitialState P f G x₀ none).normConstant

variable {P : Parameters}
variable {f : EuclideanSpace ℝ (Fin n) → ℝ}
variable {G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
variable {H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
variable {x₀ center : EuclideanSpace ℝ (Fin n)}

/-- Actual selected-model G1--G4 imply first-unit acceptance and inactive
safeguard, including when function-value correction is enabled. -/
theorem PracticalGrowthSource.first_accepted (D : PracticalGrowthSource P f G H x₀ center)
    (hP : P.Valid n) :
    ∃ K, ∀ k, K ≤ k →
      let S := practicalRun P f G x₀ k
      (practicalModel P S).safeDirection S = (practicalModel P S).direction ∧
        Accepted f P.armijo S.point S.gradient ((practicalModel P S).safeDirection S) 1 := by
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
  obtain ⟨K₁, hK₁⟩ := practicalRun_eventually_corrected_data P hP f G H x₀ center
    D.f_deriv D.g_deriv D.h_cont.self_of_nhds D.sourceRadius D.sourceRadius_pos D.hessianLipschitz D.h_lip
    D.mu D.mu_pos D.coercive D.converges D.distinct epsilon he
  obtain ⟨K₂, hK₂⟩ := practicalRun_eventually_retains_window P hP f G H x₀ center
    D.f_deriv D.g_deriv D.h_cont.self_of_nhds D.mu D.sigma D.mu_pos D.sigma_pos D.coercive
    D.converges D.distinct D.gainStart D.gain
  obtain ⟨K₃, hK₃⟩ := practicalRun_eventually_incoming_nonempty P hP f G H x₀ center
    D.f_deriv D.g_deriv D.h_cont.self_of_nhds D.mu D.mu_pos D.coercive D.converges D.distinct
  obtain ⟨K₄, hK₄⟩ := practicalRun_eventually_trial_data P hP f G H x₀ center
    D.f_deriv D.g_deriv D.h_cont D.mu D.mu_pos D.coercive D.converges D.distinct epsilon he
  have hsym := local_hessian_symmetric f G H center D.f_deriv D.g_deriv.self_of_nhds
  refine ⟨max D.gainStart (max D.trialStart (max K₁ (max K₂ (max K₃ K₄)))), ?_⟩
  intro k hk
  let S := practicalRun P f G x₀ k
  let M := practicalModel P S
  have hdata := hK₁ k (by omega)
  have hret : M.pairs = incomingWindow S := (hK₂ k (by omega)).2.1
  have hlen : M.pairs.length ≤ n := (practicalModel_length_le P S).trans (min_le_right _ _)
  have hp : 0 < M.pairs.length := by rw [hret]; exact hK₃ k (by omega)
  have hs (i : Fin M.pairs.length) : storedSteps M.pairs i ≠ 0 :=
    positivePair_step_ne_zero _ (practicalRun_pairs_positive P f G x₀ k _
      (practicalModel_pair_mem P S _ (List.get_mem _ i)))
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
  have ht := fun hd => D.trial k (by omega) hp (practicalModel_selected_partial P S hdom.2.2.1 hd) hd
  have htrial := fun hd => And.intro (ht hd).1 (ht hd).2.1
  have hrelated := practicalModel_selected_gradientRelated P S hp.ne' (H center) hsym
    D.mu D.sigma D.upper D.ell D.trialUpper epsilon D.mu_pos D.sigma_pos D.upper_pos D.ell_pos
    D.trialUpper_pos he.le her D.coercive D.h_norm hs hgain hy hmodel htrial
  have hc := run_cache_constants P n (practicalModel P) f G
    (algorithmInitialState P f G x₀ none) rfl rfl k
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
  have hq := practicalModel_selected_quotient P S hp.ne' f G H (H center) hsym
    D.mu D.sigma D.upper D.ell D.trialUpper epsilon D.mu_pos D.sigma_pos D.upper_pos D.ell_pos
    D.trialUpper_pos he.le her D.coercive D.h_norm hs hgain hy hmodel hTaylor.1 hc.2.1.symm htrial
    hTaylor.2.1 hTaylor.2.2.1 hTaylor.2.2.2.1 hTaylor.2.2.2.2
  refine ⟨hinactive, ?_⟩
  rw [hinactive]
  exact quotient_acceptance_from_margin (H center) (practicalSelectedDirection P S)
    _ (practicalComputedCurvature P S) C epsilon P.armijo D.eta D.ell D.ell_pos
    (by
      dsimp only at hq
      split_ifs with hd
      · simpa only [hd, ite_true] using hq
      · simpa only [hd, ite_false] using hq)
    (fun hd => ⟨(ht hd).1, (ht hd).2.2⟩) hallow


/-- Primitive source assumptions yield a genuine clean phase of the
actual executor, including exact memory and counter recurrences. -/
theorem PracticalGrowthSource.clean_phase (D : PracticalGrowthSource P f G H x₀ center)
    (hP : P.Valid n) :
    ∃ K, ∀ k, K ≤ k →
      let S := practicalRun P f G x₀ k
      let S' := practicalRun P f G x₀ (k + 1)
      (practicalModel P S).pairs = incomingWindow S ∧
        (practicalModel P S).deletedByTest = 0 ∧
        (practicalModel P S).safeDirection S = (practicalModel P S).direction ∧
        Accepted f P.armijo S.point S.gradient ((practicalModel P S).safeDirection S) 1 ∧
        S'.pairs.length = min S.capacity S.pairs.length + 1 ∧
        (S'.capacity, S'.cleanCount) = updateCapacity P n S.capacity S.cleanCount
          (min S.capacity S.pairs.length) 0 1 := by
  obtain ⟨K₁, hK₁⟩ := D.first_accepted hP
  obtain ⟨K₂, hK₂⟩ := practicalRun_eventually_retains_window P hP f G H x₀ center
    D.f_deriv D.g_deriv D.h_cont.self_of_nhds D.mu D.sigma D.mu_pos D.sigma_pos D.coercive
    D.converges D.distinct D.gainStart D.gain
  have hinit := practicalRun_initial_gradient_ne_zero P f G x₀ center D.converges D.distinct
  have hc := algorithmInitialState_constants P hP f G x₀ none hinit
  obtain ⟨K₃, hK₃⟩ := run_eventually_local_new_pairs P n (practicalModel P) f G H
    (algorithmInitialState P f G x₀ none) rfl rfl hc.1 hc.2 hP.2.2.2.2.2.2.1
    (hP.2.2.2.2.2.2.2.1.trans (by norm_num)) center D.f_deriv D.g_deriv D.h_cont.self_of_nhds
    D.mu D.mu_pos D.coercive D.converges D.distinct 1 (by norm_num)
  refine ⟨max K₁ (max K₂ K₃), ?_⟩
  intro k hk
  let S := practicalRun P f G x₀ k
  let S' := practicalRun P f G x₀ (k + 1)
  let M := practicalModel P S
  have hfirst := hK₁ k (by omega)
  have hretain := hK₂ k (by omega)
  have hnew := hK₃ k (by omega)
  dsimp only at hfirst hretain hnew ⊢
  have hsearch := outerSearch_first_accepted (practicalModel P) f G P.armijo S hfirst.2
  have hpositive : positivePair (observedTrialPair f G S (M.safeDirection S)) := by
    have hh : positivePair (observedTrialPair f G S
      ((outerSearch (practicalModel P) f G P.armijo S).length •
        (outerSearch (practicalModel P) f G P.armijo S).direction)) := hnew.2.2.2
    rw [hsearch] at hh
    simpa only [one_smul] using hh
  have hupdate := outerAdvance_clean_update P n (practicalModel P) f G S hnew.1 hfirst.2 hpositive
  have hcap : S.capacity ≤ n := ((practicalRun_memory_invariants P hP f G x₀ k).2.1).trans hP.2.2.1
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
theorem PracticalGrowthSource.eventually_maximum_window (D : PracticalGrowthSource P f G H x₀ center)
    (hP : P.Valid n) :
    ∃ K, ∀ k, K ≤ k →
      let S := practicalRun P f G x₀ k
      S.capacity = P.maximumCapacity ∧
        (practicalModel P S).pairs.length = P.maximumCapacity ∧
        (practicalModel P S).deletedByTest = 0 ∧
        (practicalModel P S).safeDirection S = (practicalModel P S).direction ∧
        Accepted f P.armijo S.point S.gradient ((practicalModel P S).safeDirection S) 1 := by
  obtain ⟨K₀, hK₀⟩ := D.clean_phase hP
  obtain ⟨K₁, hK₁⟩ := capacity_growth_eventually_of_tail P n K₀ (by have := hP.1; omega)
    hP.2.2.1 (by have := hP.2.2.2.1; omega)
    (fun k => (practicalRun P f G x₀ k).capacity)
    (fun k => (practicalRun P f G x₀ k).cleanCount)
    (fun k => (practicalRun P f G x₀ k).pairs.length)
    (fun k => (practicalRun_memory_invariants P hP f G x₀ k).2.1)
    (fun k => (practicalRun_memory_invariants P hP f G x₀ k).2.2)
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
theorem PracticalGrowthSource.clean_pair_update (D : PracticalGrowthSource P f G H x₀ center)
    (hP : P.Valid n) :
    ∃ K, ∀ k, K ≤ k →
      let S := practicalRun P f G x₀ k
      let S' := practicalRun P f G x₀ (k + 1)
      let u := (practicalModel P S).direction
      S'.point = S.point + u ∧
        S'.pairs = (incomingWindow S ++ [observedTrialPair f G S u]).map (fun a => a.transport u) := by
  obtain ⟨K₀, hK₀⟩ := D.clean_phase hP
  have hinit := practicalRun_initial_gradient_ne_zero P f G x₀ center D.converges D.distinct
  have hc := algorithmInitialState_constants P hP f G x₀ none hinit
  obtain ⟨K₁, hK₁⟩ := run_eventually_local_new_pairs P n (practicalModel P) f G H
    (algorithmInitialState P f G x₀ none) rfl rfl hc.1 hc.2 hP.2.2.2.2.2.2.1
    (hP.2.2.2.2.2.2.2.1.trans (by norm_num)) center D.f_deriv D.g_deriv D.h_cont.self_of_nhds
    D.mu D.mu_pos D.coercive D.converges D.distinct 1 (by norm_num)
  refine ⟨max K₀ K₁, ?_⟩
  intro k hk
  let S := practicalRun P f G x₀ k
  let S' := practicalRun P f G x₀ (k + 1)
  let M := practicalModel P S
  have hh := hK₀ k (by omega)
  have hnew := hK₁ k (by omega)
  dsimp only at hh hnew ⊢
  have hsearch := outerSearch_first_accepted (practicalModel P) f G P.armijo S hh.2.2.2.1
  have hpositive : positivePair (observedTrialPair f G S (M.safeDirection S)) := by
    have hp : positivePair (observedTrialPair f G S
      ((outerSearch (practicalModel P) f G P.armijo S).length •
        (outerSearch (practicalModel P) f G P.armijo S).direction)) := hnew.2.2.2
    rw [hsearch] at hp
    simpa only [one_smul] using hp
  have hu := outerAdvance_clean_update P n (practicalModel P) f G S hnew.1 hh.2.2.2.1 hpositive
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
theorem PracticalGrowthSource.corrected_gates (D : PracticalGrowthSource P f G H x₀ center)
    (hP : P.Valid n) (hon : P.valuesEnabled = true) :
    ∃ K, ∀ k, K ≤ k →
      let W := (practicalModel P (practicalRun P f G x₀ k)).pairs
      (∀ i : Fin W.length, |12 * storedSplit W i * (W.get i).valueDefect| ≤ storedPairing W i i / 2) ∧
        correctedWindowPasses P.windowThreshold W ∧ selectedModel P W = storedValueModel W :=
  practicalRun_eventually_corrected_gates P hP hon f G H x₀ center D.f_deriv D.g_deriv
    D.h_cont.self_of_nhds D.sourceRadius D.sourceRadius_pos D.hessianLipschitz D.h_lip D.mu D.sigma
    D.mu_pos D.sigma_pos D.coercive D.converges D.distinct D.gainStart D.gain

end
end krylov.XR
