import krylov.XR.EuclideanPracticalSource

/-!
# Full initial memory for practical XR

Article Theorem 7.3: when the initial capacity is the dimension, G3 is
unnecessary. Both genuine model calls retain their incoming windows by G2,
including after a rejected probe; positive accepted observations then fill
the window before unit acceptance or a local rate is invoked.
-/
namespace krylov.XR
noncomputable section
open Set Metric Filter Topology krylov.Methods
open scoped InnerProductSpace NNReal
variable {n : ℕ}
set_option maxHeartbeats 800000

/-- Every pair of the actual unchanged-anchor probe state is positive,
independently of whether the new probe passes its insertion guard. -/
theorem euclideanPractical_firstProbeState_positive (P : Parameters)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (S : State (EuclideanSpace ℝ (Fin n))) (hS : ∀ a ∈ S.pairs, positivePair a) :
    ∀ a ∈ (firstProbeState (euclideanPracticalModel P) f G S).pairs, positivePair a := by
  exact appendPositive_positive _ _ (fun a ha => hS a (euclideanPracticalModel_pair_mem P S a ha))

/-- All observations of the actual probe state eventually approximate the
limiting Hessian relatively, without a probe-query localization premise. -/
theorem euclideanPracticalRun_eventually_probe_secant_errors (P : Parameters) (hP : P.Valid n)
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
    ∃ K, ∀ k, K ≤ k →
      ∀ a ∈ (firstProbeState (euclideanPracticalModel P) f G (euclideanPracticalRun P f G x₀ k)).pairs,
        ‖a.image - H center a.step‖ ≤ (epsilon : ℝ) * ‖a.step‖ := by
  have hclose : ∀ᶠ z in 𝓝 center, ‖H z - H center‖ < (epsilon : ℝ) :=
    (hH.sub continuousAt_const).norm.eventually (gt_mem_nhds (by
      change ‖H center - H center‖ < (epsilon : ℝ)
      simpa only [sub_self, norm_zero] using hepsilon))
  have hdata : ∀ᶠ z in 𝓝 center, HasFDerivAt G (H z) z ∧ ‖H z - H center‖ ≤ (epsilon : ℝ) := by
    filter_upwards [hG, hclose] with z hg hh
    exact ⟨hg, hh.le⟩
  obtain ⟨radius, hradius, hlocal⟩ := Metric.eventually_nhds_iff.mp hdata
  obtain ⟨K₁, hK₁⟩ := euclideanPracticalRun_eventually_secant_errors P hP f G H x₀ center
    hF hG hH mu hmu hpositive hconv hne epsilon hepsilon
  have hinit := euclideanPracticalRun_initial_gradient_ne_zero P f G x₀ center hconv hne
  have hc := algorithmInitialState_constants P hP f G x₀ none hinit
  obtain ⟨K₂, hK₂⟩ := run_eventually_local_new_pairs P n (euclideanPracticalModel P) f G H
    (algorithmInitialState P f G x₀ none) rfl rfl hc.1 hc.2 hP.2.2.2.2.2.2.1
    (hP.2.2.2.2.2.2.2.1.trans (by norm_num)) center hF hG hH mu hmu hpositive hconv hne radius hradius
  refine ⟨max K₁ K₂, ?_⟩
  intro k hk
  let S := euclideanPracticalRun P f G x₀ k
  let M := euclideanPracticalModel P S
  let u := M.safeDirection S
  have hnear := (hK₂ k (by omega)).2.1
  have herr := local_secant_error G H (H center) center radius epsilon
    (fun z hz => (hlocal hz).1) (fun z hz => (hlocal hz).2) S.point (S.point + u)
    (by change ‖S.point - center‖ < radius; exact hnear.1)
    (by change ‖S.point + u - center‖ < radius; exact hnear.2)
  have hcache := run_cache_constants P n (euclideanPracticalModel P) f G
    (algorithmInitialState P f G x₀ none) rfl rfl k
  have hnew : ‖(observedTrialPair f G S u).image - H center (observedTrialPair f G S u).step‖ ≤
      (epsilon : ℝ) * ‖(observedTrialPair f G S u).step‖ := by
    change ‖G (S.point + u) - S.gradient - H center u‖ ≤ (epsilon : ℝ) * ‖u‖
    rw [show S.gradient = G S.point from hcache.2.1]
    simpa only [add_sub_cancel_left] using herr
  exact appendPositive_all _ _ (fun a => ‖a.image - H center a.step‖ ≤ (epsilon : ℝ) * ‖a.step‖)
    (fun a ha => hK₁ k (by omega) a (euclideanPracticalModel_pair_mem P S a ha)) hnew

/-- Original G2 at the actually visited second ModelStep forces its full
incoming-window retention too; no adequacy assumption is needed. -/
theorem euclideanPracticalRun_eventually_probe_retains_window (P : Parameters) (hP : P.Valid n)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (x₀ center : EuclideanSpace ℝ (Fin n))
    (hF : ∀ᶠ z in 𝓝 center, HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ᶠ z in 𝓝 center, HasFDerivAt G (H z) z) (hH : ContinuousAt H center)
    (mu sigma : ℝ) (hmu : 0 < mu) (hsigma : 0 < sigma)
    (hpositive : ∀ v, mu * ‖v‖ ^ 2 ≤ inner ℝ v (H center v))
    (hconv : Tendsto (fun k => (euclideanPracticalRun P f G x₀ k).point) atTop (𝓝 center))
    (hne : ∀ k, (euclideanPracticalRun P f G x₀ k).point ≠ center)
    (K₀ : ℕ)
    (hgain : ∀ k, K₀ ≤ k →
      let S := euclideanPracticalRun P f G x₀ k
      ¬Accepted f P.armijo S.point S.gradient ((euclideanPracticalModel P S).safeDirection S) 1 →
      let W := incomingWindow (firstProbeState (euclideanPracticalModel P) f G S)
      ∀ w : Fin W.length → ℝ, sigma ^ 2 * ‖WithLp.toLp 2 w‖ ^ 2 ≤
        ‖combine (krylov.Convergence.unitWindow (storedSteps W)) w‖ ^ 2) :
    ∃ K, ∀ k, K ≤ k →
      let S := euclideanPracticalRun P f G x₀ k
      ¬Accepted f P.armijo S.point S.gradient ((euclideanPracticalModel P S).safeDirection S) 1 →
      let S₁ := firstProbeState (euclideanPracticalModel P) f G S
      rankDeletion (incomingWindow S₁) = 0 ∧
        (euclideanPracticalModel P S₁).pairs = incomingWindow S₁ ∧
        (euclideanPracticalModel P S₁).pairsBeforeTest = (incomingWindow S₁).length ∧
        (euclideanPracticalModel P S₁).deletedByTest = 0 := by
  have htheta : 0 < P.windowThreshold := hP.2.2.2.2.2.1
  have hcoerc : 0 < localCoercivity mu sigma := by unfold localCoercivity; positivity
  let epsilon : ℝ := min (mu * sigma ^ 2 / (8 * ((n : ℝ) + 1)))
    (P.windowThreshold * localCoercivity mu sigma / (4 * ((n : ℝ) + 1)))
  have hepsilon : 0 < epsilon := by dsimp only [epsilon]; positivity
  let e : ℝ≥0 := ⟨epsilon, hepsilon.le⟩
  have hsmall : (n : ℝ) * epsilon ≤ mu * sigma ^ 2 / 4 := by
    have h := (le_div_iff₀ (by positivity : 0 < 8 * ((n : ℝ) + 1))).mp
      (min_le_left (mu * sigma ^ 2 / (8 * ((n : ℝ) + 1)))
        (P.windowThreshold * localCoercivity mu sigma / (4 * ((n : ℝ) + 1))))
    change epsilon * (8 * ((n : ℝ) + 1)) ≤ _ at h
    nlinarith
  have hgate : 2 * (n : ℝ) * epsilon / localCoercivity mu sigma < P.windowThreshold := by
    have h := (le_div_iff₀ (by positivity : 0 < 4 * ((n : ℝ) + 1))).mp
      (min_le_right (mu * sigma ^ 2 / (8 * ((n : ℝ) + 1)))
        (P.windowThreshold * localCoercivity mu sigma / (4 * ((n : ℝ) + 1))))
    change epsilon * (4 * ((n : ℝ) + 1)) ≤ _ at h
    apply (div_lt_iff₀ hcoerc).2
    nlinarith [mul_pos htheta hcoerc]
  have hsym := local_hessian_symmetric f G H center hF hG.self_of_nhds
  obtain ⟨K₁, hK₁⟩ := euclideanPracticalRun_eventually_probe_secant_errors P hP f G H x₀ center
    hF hG hH mu hmu hpositive hconv hne e hepsilon
  refine ⟨max K₀ K₁, ?_⟩
  intro k hk
  dsimp only
  intro hreject
  let S := euclideanPracticalRun P f G x₀ k
  let S₁ := firstProbeState (euclideanPracticalModel P) f G S
  have hlen : (incomingWindow S₁).length ≤ n := by
    simp only [incomingWindow, retainNewest_length]
    omega
  have hlenR : ((incomingWindow S₁).length : ℝ) ≤ n := by exact_mod_cast hlen
  have hy i : ‖storedImages (incomingWindow S₁) i - H center (storedSteps (incomingWindow S₁) i)‖ ≤
      epsilon * ‖storedSteps (incomingWindow S₁) i‖ :=
    hK₁ k (by omega) _ (List.mem_of_mem_drop (List.get_mem _ i))
  exact algorithmModel_local_retention P htheta S₁
    (euclideanPractical_firstProbeState_positive P f G S (euclideanPracticalRun_pairs_positive P f G x₀ k))
    (H center) hsym mu sigma epsilon hmu hsigma hepsilon.le hpositive (hgain k (by omega) hreject) hy
    ((mul_le_mul_of_nonneg_right hlenR hepsilon.le).trans hsmall)
    ((div_le_div_of_nonneg_right (by nlinarith [mul_le_mul_of_nonneg_right hlenR hepsilon.le])
      hcoerc.le).trans_lt hgate)


/-- With full capacity, no actual cleanup deletion means the sole probe
cannot reduce the number of pairs reaching the accepted search. -/
theorem euclideanPractical_outerSearch_full_length_ge (P : Parameters)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (S : State (EuclideanSpace ℝ (Fin n))) (hcap : S.capacity = n)
    (hfirst : (euclideanPracticalModel P S).pairs = incomingWindow S)
    (hsecond : ¬Accepted f P.armijo S.point S.gradient ((euclideanPracticalModel P S).safeDirection S) 1 →
      (euclideanPracticalModel P (firstProbeState (euclideanPracticalModel P) f G S)).pairs =
        incomingWindow (firstProbeState (euclideanPracticalModel P) f G S)) :
    min n S.pairs.length ≤ (outerSearch (euclideanPracticalModel P) f G P.armijo S).pairs.length := by
  classical
  let S₁ := firstProbeState (euclideanPracticalModel P) f G S
  have hcount : (euclideanPracticalModel P S).pairs.length = min n S.pairs.length := by
    rw [hfirst]
    simp only [incomingWindow, retainNewest_length, hcap, min_self]
  unfold outerSearch
  dsimp only
  split
  · exact hcount.ge
  · rename_i hreject
    change min n S.pairs.length ≤ (euclideanPracticalModel P S₁).pairs.length
    rw [hsecond hreject]
    have hlen : (euclideanPracticalModel P S).pairs.length ≤ S₁.pairs.length :=
      appendPositive_length_ge _ _
    simp only [incomingWindow, retainNewest_length]
    change min n S.pairs.length ≤ min (min S.capacity n) S₁.pairs.length
    rw [hcap, min_self]
    omega

/-- The actual accepted positive observation raises the retained count,
including when the first probe was rejected and recomputed. -/
theorem euclideanPractical_outerAdvance_full_length_ge (P : Parameters)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (S : State (EuclideanSpace ℝ (Fin n))) (hg : S.gradient ≠ 0) (hcap : S.capacity = n)
    (hfirst : (euclideanPracticalModel P S).pairs = incomingWindow S)
    (hsecond : ¬Accepted f P.armijo S.point S.gradient ((euclideanPracticalModel P S).safeDirection S) 1 →
      (euclideanPracticalModel P (firstProbeState (euclideanPracticalModel P) f G S)).pairs =
        incomingWindow (firstProbeState (euclideanPracticalModel P) f G S))
    (hpositive : positivePair (observedTrialPair f G S
      ((outerSearch (euclideanPracticalModel P) f G P.armijo S).length •
        (outerSearch (euclideanPracticalModel P) f G P.armijo S).direction))) :
    min n S.pairs.length + 1 ≤ (outerAdvance P n (euclideanPracticalModel P) f G S).pairs.length := by
  classical
  have hlen := euclideanPractical_outerSearch_full_length_ge P f G S hcap hfirst hsecond
  simp only [outerAdvance, ite_eq_right hg]
  rw [List.length_map, appendPositive, ite_eq_left hpositive, List.length_append, List.length_singleton]
  omega



/-- Full initial capacity reaches an actual full retained window from
G1 and G2, without any assumption about the computed trial curvature. -/
theorem euclideanPracticalRun_eventually_full_of_initial_full (P : Parameters) (hP : P.Valid n)
    (hfull : P.initialCapacity = n)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (x₀ center : EuclideanSpace ℝ (Fin n))
    (hF : ∀ᶠ z in 𝓝 center, HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ᶠ z in 𝓝 center, HasFDerivAt G (H z) z) (hH : ContinuousAt H center)
    (mu sigma : ℝ) (hmu : 0 < mu) (hsigma : 0 < sigma)
    (hpositive : ∀ v, mu * ‖v‖ ^ 2 ≤ inner ℝ v (H center v))
    (hconv : Tendsto (fun k => (euclideanPracticalRun P f G x₀ k).point) atTop (𝓝 center))
    (hne : ∀ k, (euclideanPracticalRun P f G x₀ k).point ≠ center)
    (K₀ : ℕ)
    (hgain : ∀ k, K₀ ≤ k →
      let W := incomingWindow (euclideanPracticalRun P f G x₀ k)
      ∀ w : Fin W.length → ℝ, sigma ^ 2 * ‖WithLp.toLp 2 w‖ ^ 2 ≤
        ‖combine (krylov.Convergence.unitWindow (storedSteps W)) w‖ ^ 2)
    (hprobeGain : ∀ k, K₀ ≤ k →
      let S := euclideanPracticalRun P f G x₀ k
      ¬Accepted f P.armijo S.point S.gradient ((euclideanPracticalModel P S).safeDirection S) 1 →
      let W := incomingWindow (firstProbeState (euclideanPracticalModel P) f G S)
      ∀ w : Fin W.length → ℝ, sigma ^ 2 * ‖WithLp.toLp 2 w‖ ^ 2 ≤
        ‖combine (krylov.Convergence.unitWindow (storedSteps W)) w‖ ^ 2) :
    ∃ K, ∀ k, K ≤ k → (euclideanPracticalModel P (euclideanPracticalRun P f G x₀ k)).pairs.length = n := by
  obtain ⟨K₁, hK₁⟩ := euclideanPracticalRun_eventually_retains_window P hP f G H x₀ center
    hF hG hH mu sigma hmu hsigma hpositive hconv hne K₀ hgain
  obtain ⟨K₂, hK₂⟩ := euclideanPracticalRun_eventually_probe_retains_window P hP f G H x₀ center
    hF hG hH mu sigma hmu hsigma hpositive hconv hne K₀ hprobeGain
  have hinit := euclideanPracticalRun_initial_gradient_ne_zero P f G x₀ center hconv hne
  have hc := algorithmInitialState_constants P hP f G x₀ none hinit
  obtain ⟨K₃, hK₃⟩ := run_eventually_local_new_pairs P n (euclideanPracticalModel P) f G H
    (algorithmInitialState P f G x₀ none) rfl rfl hc.1 hc.2 hP.2.2.2.2.2.2.1
    (hP.2.2.2.2.2.2.2.1.trans (by norm_num)) center hF hG hH mu hmu hpositive hconv hne 1 (by norm_num)
  let K := max K₁ (max K₂ K₃)
  have hcap (k : ℕ) : (euclideanPracticalRun P f G x₀ k).capacity = n := by
    have hh := euclideanPracticalRun_memory_invariants P hP f G x₀ k
    have hi := hP.2.2.1
    rw [hfull] at hh
    omega
  have hstep (k : ℕ) (hk : K ≤ k) :
      min n (euclideanPracticalRun P f G x₀ k).pairs.length + 1 ≤
        (euclideanPracticalRun P f G x₀ (k + 1)).pairs.length := by
    have hfirst := (hK₁ k (by dsimp only [K] at hk; omega)).2.1
    have hnew := hK₃ k (by dsimp only [K] at hk; omega)
    exact euclideanPractical_outerAdvance_full_length_ge P f G _ hnew.1 (hcap k) hfirst
      (fun hr => (hK₂ k (by dsimp only [K] at hk; omega) hr).2.1) hnew.2.2.2
  have hfilled := length_fills_of_tail (fun k => (euclideanPracticalRun P f G x₀ k).pairs.length) n K hstep
  refine ⟨K + n, ?_⟩
  intro k hk
  rw [(hK₁ k (by dsimp only [K] at hk; omega)).2.1]
  simp only [incomingWindow, retainNewest_length, hcap k, min_self, min_eq_left (hfilled k hk)]



/-- The original full-initial-memory source admits a genuine selected-model
local-source certificate with no partial-trial adequacy premise. This
constructor feeds the actual SS1-F execution and rate dictionaries. -/
theorem euclideanPracticalGrowthSource_exists_of_initial_full (P : Parameters) (hP : P.Valid n)
    (hfull : P.initialCapacity = n)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (x₀ center : EuclideanSpace ℝ (Fin n))
    (hF : ∀ᶠ z in 𝓝 center, HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ᶠ z in 𝓝 center, HasFDerivAt G (H z) z)
    (hHC : ∀ᶠ z in 𝓝 center, ContinuousAt H z)
    (radius : ℝ) (hradius : 0 < radius) (L : ℝ≥0)
    (hLip : LipschitzOnWith L H (ball center radius))
    (mu sigma upper ell trialUpper eta : ℝ)
    (hmu : 0 < mu) (hsigma : 0 < sigma) (hupper : 0 < upper)
    (hell : 0 < ell) (htrialUpper : 0 < trialUpper) (heta : 0 < eta)
    (hpositive : ∀ v, mu * ‖v‖ ^ 2 ≤ inner ℝ v (H center v)) (hHnorm : ‖H center‖ ≤ upper)
    (hconv : Tendsto (fun k => (euclideanPracticalRun P f G x₀ k).point) atTop (𝓝 center))
    (hne : ∀ k, (euclideanPracticalRun P f G x₀ k).point ≠ center)
    (K₀ : ℕ)
    (hgain : ∀ k, K₀ ≤ k →
      let W := incomingWindow (euclideanPracticalRun P f G x₀ k)
      ∀ w : Fin W.length → ℝ, sigma ^ 2 * ‖WithLp.toLp 2 w‖ ^ 2 ≤
        ‖combine (krylov.Convergence.unitWindow (storedSteps W)) w‖ ^ 2)
    (hprobeGain : ∀ k, K₀ ≤ k →
      let S := euclideanPracticalRun P f G x₀ k
      ¬Accepted f P.armijo S.point S.gradient ((euclideanPracticalModel P S).safeDirection S) 1 →
      let W := incomingWindow (firstProbeState (euclideanPracticalModel P) f G S)
      ∀ w : Fin W.length → ℝ, sigma ^ 2 * ‖WithLp.toLp 2 w‖ ^ 2 ≤
        ‖combine (krylov.Convergence.unitWindow (storedSteps W)) w‖ ^ 2)
    (hG₄₁ : (algorithmInitialState P f G x₀ none).descentConstant <
      dimensionDescentConstant n mu sigma upper trialUpper)
    (hG₄₂ : dimensionNormConstant n mu sigma upper ell <
      (algorithmInitialState P f G x₀ none).normConstant) :
    Nonempty (EuclideanPracticalGrowthSource P f G H x₀ center) := by
  obtain ⟨K, hK⟩ := euclideanPracticalRun_eventually_full_of_initial_full P hP hfull f G H x₀ center
    hF hG hHC.self_of_nhds mu sigma hmu hsigma hpositive hconv hne K₀ hgain hprobeGain
  let D : EuclideanPracticalGrowthSource P f G H x₀ center :=
    { mu := mu, sigma := sigma, upper := upper, ell := ell, trialUpper := trialUpper, eta := eta
      mu_pos := hmu, sigma_pos := hsigma, upper_pos := hupper, ell_pos := hell
      trialUpper_pos := htrialUpper, eta_pos := heta, f_deriv := hF, g_deriv := hG, h_cont := hHC
      sourceRadius := radius, sourceRadius_pos := hradius, hessianLipschitz := L, h_lip := hLip
      coercive := hpositive, h_norm := hHnorm, converges := hconv, distinct := hne
      gainStart := K₀, gain := hgain, trialStart := K
      trial := by
        intro k hk
        dsimp only
        intro _ hp
        have hh := hK k hk
        omega
      safeguard_descent := hG₄₁, safeguard_norm := hG₄₂ }
  exact ⟨D⟩

end
end krylov.XR
