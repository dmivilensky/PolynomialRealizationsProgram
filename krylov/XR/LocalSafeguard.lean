import krylov.XR.LocalRetention
import krylov.XR.LocalNonempty
import krylov.XR.LocalModelStep

/-!
Article: main_krylov, thm:grow, eventual inactivity of (G).
Use: derive the actual branch decision from G1, incoming-window G2,
the two primitive partial-window curvature bounds of G3, and G4.
In particular no successful safeguard test is assumed. The constants
are fixed before all executed window sizes. Source: the proved primitive
local model bounds and exact diagonal normalization of real secants.
-/

namespace krylov.XR
noncomputable section
open Set Metric Filter Topology krylov.Methods
open scoped InnerProductSpace NNReal
variable {n : ℕ}

/-- The original local assumptions force safeguard (G) to be inactive on
every sufficiently late first ModelStep of the literal algorithm. G3 is
used only for a genuine nonzero new direction in a partial window. -/
theorem algorithmRun_eventually_safeguard_inactive (P : Parameters) (hP : P.Valid n)
    (hoff : P.valuesEnabled = false)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (x₀ center : EuclideanSpace ℝ (Fin n)) (bounds : SpectralBounds)
    (hF : ∀ᶠ z in 𝓝 center, HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ᶠ z in 𝓝 center, HasFDerivAt G (H z) z) (hH : ContinuousAt H center)
    (mu sigma upper ell trialUpper : ℝ)
    (hmu : 0 < mu) (hsigma : 0 < sigma) (hupper : 0 < upper)
    (hell : 0 < ell) (htrialUpper : 0 < trialUpper)
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
          ‖modelDirection (storedSteps M.pairs) (storedImages M.pairs) (storedModel M.pairs) S.gradient‖ ^ 2)
    (hG₄₁ : (algorithmInitialState P f G x₀ bounds).descentConstant <
      dimensionDescentConstant n mu sigma upper trialUpper)
    (hG₄₂ : dimensionNormConstant n mu sigma upper ell <
      (algorithmInitialState P f G x₀ bounds).normConstant) :
    ∃ K, ∀ k, K ≤ k →
      let S := algorithmRun P f G x₀ bounds k
      (algorithmModel P S).safeDirection S = (algorithmModel P S).direction := by
  have hconst := dimension_constants_positive n mu sigma upper ell trialUpper hmu hsigma hupper hell
  let epsilon : ℝ := dimensionStepRadius n mu sigma upper / 2
  have he : 0 < epsilon := div_pos hconst.1 (by norm_num)
  have her : epsilon ≤ dimensionStepRadius n mu sigma upper := by dsimp only [epsilon]; linarith
  let e : ℝ≥0 := ⟨epsilon, he.le⟩
  obtain ⟨K₁, hK₁⟩ := algorithmRun_eventually_secant_errors P hP f G H x₀ center bounds
    hF hG hH mu hmu hpositive hconv hne e he
  obtain ⟨K₂, hK₂⟩ := algorithmRun_eventually_retains_window P hP f G H x₀ center bounds
    hF hG hH mu sigma hmu hsigma hpositive hconv hne K₀ hgain
  obtain ⟨K₄, hK₄⟩ := algorithmRun_eventually_incoming_nonempty P hP f G H x₀ center bounds
    hF hG hH mu hmu hpositive hconv hne
  have hsym := local_hessian_symmetric f G H center hF hG.self_of_nhds
  refine ⟨max (max K₀ K₁) (max K₂ (max K₃ K₄)), ?_⟩
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
  have hrelated := algorithmModel_local_gradientRelated P hoff S hp.ne' (H center) hsym
    mu sigma upper ell trialUpper epsilon hmu hsigma hupper hell htrialUpper he.le her
    hpositive hHnorm hs hgain hy ht
  have hc := run_cache_constants P n (algorithmModel P) f G
    (algorithmInitialState P f G x₀ bounds) rfl rfl k
  exact safeguard_eq_of_stronger_bounds S.descentConstant S.normConstant
    (dimensionDescentConstant n mu sigma upper trialUpper) (dimensionNormConstant n mu sigma upper ell)
    M.fallbackCurvature S.gradient M.direction hrelated
    (by rw [show S.descentConstant = _ from hc.2.2.1]; exact hG₄₁.le)
    (by rw [show S.normConstant = _ from hc.2.2.2]; exact hG₄₂.le)

end
end krylov.XR
