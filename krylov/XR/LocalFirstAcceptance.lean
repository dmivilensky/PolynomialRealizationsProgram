import krylov.XR.LocalSafeguard
import krylov.XR.LocalTrialData
import krylov.XR.LocalUnitAcceptance

/-!
Article: main_krylov, thm:grow, eventual acceptance of the first trial.
Use: combine G1--G4 with the genuine local memory and measured Taylor
theorems. Every point/segment domain, inverse domain, nonzero denominator
and inactive safeguard is proved from the function and the real executor.
Source: primitive local secant estimates and the positive G3 margin.
-/

namespace krylov.XR
noncomputable section
open Set Metric Filter Topology krylov.Methods
open scoped InnerProductSpace NNReal
variable {n : ℕ}
set_option maxHeartbeats 800000

/-- Original local C² data and partial-window adequacy force every late
first trial to pass the actual Armijo test of the literal algorithm. -/
theorem algorithmRun_eventually_first_accepted (P : Parameters) (hP : P.Valid n)
    (hoff : P.valuesEnabled = false)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (x₀ center : EuclideanSpace ℝ (Fin n)) (bounds : SpectralBounds)
    (hF : ∀ᶠ z in 𝓝 center, HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ᶠ z in 𝓝 center, HasFDerivAt G (H z) z)
    (hHC : ∀ᶠ z in 𝓝 center, ContinuousAt H z)
    (mu sigma upper ell trialUpper eta : ℝ)
    (hmu : 0 < mu) (hsigma : 0 < sigma) (hupper : 0 < upper)
    (hell : 0 < ell) (htrialUpper : 0 < trialUpper) (heta : 0 < eta)
    (hpositive : ∀ v, mu * ‖v‖ ^ 2 ≤ inner ℝ v (H center v)) (hHnorm : ‖H center‖ ≤ upper)
    (hconv : Tendsto (fun k => (algorithmRun P f G x₀ bounds k).point) atTop (𝓝 center))
    (hne : ∀ k, (algorithmRun P f G x₀ bounds k).point ≠ center)
    (K₀ : ℕ)
    (hgain : ∀ k, K₀ ≤ k →
      let W := incomingWindow (algorithmRun P f G x₀ bounds k)
      ∀ w : Fin W.length → ℝ, sigma ^ 2 * ‖WithLp.toLp 2 w‖ ^ 2 ≤
        ‖combine (krylov.Convergence.unitWindow (storedSteps W)) w‖ ^ 2)
    (K₃ : ℕ)
    (htrial : ∀ k, K₃ ≤ k →
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
          (2 * (1 - P.armijo) - eta) * algorithmComputedCurvature P S)
    (hG₄₁ : (algorithmInitialState P f G x₀ bounds).descentConstant <
      dimensionDescentConstant n mu sigma upper trialUpper)
    (hG₄₂ : dimensionNormConstant n mu sigma upper ell <
      (algorithmInitialState P f G x₀ bounds).normConstant) :
    ∃ K, ∀ k, K ≤ k →
      let S := algorithmRun P f G x₀ bounds k
      (algorithmModel P S).safeDirection S = (algorithmModel P S).direction ∧
        Accepted f P.armijo S.point S.gradient ((algorithmModel P S).safeDirection S) 1 := by
  have hH := hHC.self_of_nhds
  have hconst := dimension_constants_positive n mu sigma upper ell trialUpper hmu hsigma hupper hell
  have harmijo : P.armijo < 1 / 2 := hP.2.2.2.2.2.2.2.1
  let margin : ℝ := min (1 - 2 * P.armijo) eta
  have hmargin : 0 < margin := lt_min (by linarith) heta
  let C := dimensionQuotientConstant n mu sigma ell
  let epsilon : ℝ := min (dimensionStepRadius n mu sigma upper / 2) (margin / (|C| + 1))
  have he : 0 < epsilon := lt_min (div_pos hconst.1 (by norm_num))
    (div_pos hmargin (by positivity))
  have her : epsilon ≤ dimensionStepRadius n mu sigma upper := by
    have hh := min_le_left (dimensionStepRadius n mu sigma upper / 2) (margin / (|C| + 1))
    change epsilon ≤ _ at hh
    linarith [hconst.1]
  have hallow : C * epsilon ≤ margin := by
    have hb := (le_div_iff₀ (by positivity : 0 < |C| + 1)).mp
      (min_le_right (dimensionStepRadius n mu sigma upper / 2) (margin / (|C| + 1)))
    change epsilon * (|C| + 1) ≤ margin at hb
    have hm := mul_le_mul_of_nonneg_right (le_abs_self C) he.le
    nlinarith
  let e : ℝ≥0 := ⟨epsilon, he.le⟩
  obtain ⟨K₁, hK₁⟩ := algorithmRun_eventually_secant_errors P hP f G H x₀ center bounds
    hF hG hH mu hmu hpositive hconv hne e he
  obtain ⟨K₂, hK₂⟩ := algorithmRun_eventually_retains_window P hP f G H x₀ center bounds
    hF hG hH mu sigma hmu hsigma hpositive hconv hne K₀ hgain
  obtain ⟨K₄, hK₄⟩ := algorithmRun_eventually_incoming_nonempty P hP f G H x₀ center bounds
    hF hG hH mu hmu hpositive hconv hne
  obtain ⟨K₅, hK₅⟩ := algorithmRun_eventually_safeguard_inactive P hP hoff f G H x₀ center bounds
    hF hG hH mu sigma upper ell trialUpper hmu hsigma hupper hell htrialUpper hpositive hHnorm
    hconv hne K₀ hgain K₃ (by
      intro k hk
      dsimp only
      intro hp hn hd
      have h := htrial k hk hp hn hd
      exact ⟨h.1, h.2.1⟩) hG₄₁ hG₄₂
  obtain ⟨K₆, hK₆⟩ := algorithmRun_eventually_trial_data P hP f G H x₀ center bounds
    hF hG hHC mu hmu hpositive hconv hne epsilon he
  have hsym := local_hessian_symmetric f G H center hF hG.self_of_nhds
  refine ⟨max (max K₀ K₁) (max K₂ (max K₃ (max K₄ (max K₅ K₆)))), ?_⟩
  intro k hk
  let S := algorithmRun P f G x₀ bounds k
  let M := algorithmModel P S
  have hret : M.pairs = incomingWindow S := (hK₂ k (by omega)).2.1
  have hlen : M.pairs.length ≤ n := (algorithmModel_length_le P S).trans (min_le_right _ _)
  have hp : 0 < M.pairs.length := by rw [hret]; exact hK₄ k (by omega)
  have hs (i : Fin M.pairs.length) : storedSteps M.pairs i ≠ 0 := by
    apply positivePair_step_ne_zero
    exact algorithmRun_pairs_positive P f G x₀ bounds k _
      (algorithmModel_pair_mem P S _ (List.get_mem _ i))
  have hy (i : Fin M.pairs.length) : ‖storedImages M.pairs i - H center (storedSteps M.pairs i)‖ ≤
      epsilon * ‖storedSteps M.pairs i‖ :=
    hK₁ k (by omega) _ (algorithmModel_pair_mem P S _ (List.get_mem _ i))
  have hgain : ∀ w : Fin M.pairs.length → ℝ, sigma ^ 2 * ‖WithLp.toLp 2 w‖ ^ 2 ≤
      ‖combine (krylov.Convergence.unitWindow (storedSteps M.pairs)) w‖ ^ 2 := by
    rw [hret]
    exact hgain k (by omega)
  have hsmall := (localStepRadius_small mu sigma upper epsilon hmu hsigma hupper he.le
    (her.trans (prefixMinimum_le _ n M.pairs.length hlen))).2.1
  have hdom := local_raw_window_domains (H center) hsym (storedSteps M.pairs) (storedImages M.pairs)
    hs mu sigma epsilon hmu hsigma he.le hpositive hgain hy hsmall
  have ht := fun hd => htrial k (by omega) hp
    (algorithmModel_partial_of_direction_ne_zero P S hdom.2.2.1 hd) hd
  have hinactive := hK₅ k (by omega)
  have hdata := hK₆ k (by omega)
  dsimp only at hinactive hdata ⊢
  rw [hinactive] at hdata
  have hc := run_cache_constants P n (algorithmModel P) f G
    (algorithmInitialState P f G x₀ bounds) rfl rfl k
  refine ⟨hinactive, ?_⟩
  rw [hinactive]
  exact algorithmModel_unit_accepted P hoff S hp.ne' f G H (H center) hsym
    mu sigma upper ell trialUpper epsilon eta hmu hsigma hupper hell htrialUpper he.le heta
    harmijo her hallow hpositive hHnorm hs hgain hy hdata.1 hc.2.1.symm ht
    hdata.2.1 hdata.2.2.1 hdata.2.2.2.1 hdata.2.2.2.2

end
end krylov.XR
