import krylov.XR.LocalAlgorithmStationary
import krylov.XR.LocalSecants
import krylov.XR.MemorySuffix

/-!
Article: main_krylov, G1 and proof of thm:grow, genuine local observations.
Use: derive locality and positivity of every new accepted secant and
locality of the optional rejected probe from the original local C² source
and accepted convergence. No query bound or accepted-pair hypothesis is
supplied. Source: local stationarity, internal safeguard localization and
actual local positive secants.
-/

namespace krylov.XR
noncomputable section
open Set Metric Filter Topology
open scoped InnerProductSpace NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Under the original G1 source, all newly observed segments are
eventually genuinely local and each accepted positive-curvature pair is
really inserted. The sole rejected probe is included in the conclusion. -/
theorem run_eventually_local_new_pairs (P : Parameters) (dimension : ℕ)
    (model : State E → ModelResult E) (f : E → ℝ) (G : E → E) (H : E → E →L[ℝ] E)
    (S₀ : State E) (hf₀ : S₀.value = f S₀.point) (hg₀ : S₀.gradient = G S₀.point)
    (hc₁ : 0 < S₀.descentConstant) (hc₂ : S₀.descentConstant ≤ S₀.normConstant)
    (hsigma : 0 < P.armijo) (hsigma₁ : P.armijo < 1)
    (center : E) (hF : ∀ᶠ z in 𝓝 center, HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ᶠ z in 𝓝 center, HasFDerivAt G (H z) z) (hH : ContinuousAt H center)
    (mu : ℝ) (hmu : 0 < mu) (hpositive : ∀ v, mu * ‖v‖ ^ 2 ≤ inner ℝ v (H center v))
    (hconv : Tendsto (fun k => (run P dimension model f G S₀ k).point) atTop (𝓝 center))
    (hne : ∀ k, (run P dimension model f G S₀ k).point ≠ center)
    (radius : ℝ) (hradius : 0 < radius) :
    ∃ K, ∀ k, K ≤ k →
      let S := run P dimension model f G S₀ k
      let R := outerSearch model f G P.armijo S
      S.gradient ≠ 0 ∧ PairNear center radius (observedTrialPair f G S ((model S).safeDirection S)) ∧
        PairNear center radius (observedTrialPair f G S (R.length • R.direction)) ∧
          positivePair (observedTrialPair f G S (R.length • R.direction)) := by
  let states := run P dimension model f G S₀
  obtain ⟨rG, hrG, L, hL, hFG, hLip⟩ := exists_local_gradient_data f G H center hF hG hH
  have hzero := run_local_limit_stationary P dimension model f G S₀ hf₀ hg₀ hc₁ hc₂
    hsigma hsigma₁ center rG hrG hFG L hL hLip hconv
  have hclose : ∀ᶠ z in 𝓝 center, ‖H z - H center‖ < mu / 2 :=
    (hH.sub continuousAt_const).norm.eventually (gt_mem_nhds (by
      change ‖H center - H center‖ < mu / 2
      rw [sub_self, norm_zero]
      linarith))
  have hdata : ∀ᶠ z in 𝓝 center, HasFDerivAt G (H z) z ∧ ‖H z - H center‖ ≤ mu / 2 := by
    filter_upwards [hG, hclose] with z hg hh
    exact ⟨hg, hh.le⟩
  obtain ⟨rH, hrH, hlocal⟩ := Metric.eventually_nhds_iff.mp hdata
  let epsilon : ℝ≥0 := ⟨mu / 2, by positivity⟩
  have hlocalG z (hz : z ∈ ball center rH) : HasFDerivAt G (H z) z := (hlocal hz).1
  have hlocalH z (hz : z ∈ ball center rH) : ‖H z - H center‖ ≤ (epsilon : ℝ) := (hlocal hz).2
  let A := 1 + S₀.normConstant * (L : ℝ)
  have hc₂pos : 0 < S₀.normConstant := hc₁.trans_le hc₂
  have hA : 1 ≤ A := by
    dsimp only [A]
    have hm := mul_nonneg hc₂pos.le L.coe_nonneg
    linarith
  have hApos : 0 < A := lt_of_lt_of_le (by norm_num) hA
  let delta := min rG (min radius rH / (A + 1))
  have hdelta : 0 < delta := by dsimp only [delta]; positivity
  have hnear : ∀ᶠ k in atTop, (states k).point ∈ ball center delta :=
    hconv.eventually (ball_mem_nhds center hdelta)
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.mp hnear
  refine ⟨K, ?_⟩
  intro k hk
  let S := states k
  let R := outerSearch model f G P.armijo S
  have hc := run_cache_constants P dimension model f G S₀ hf₀ hg₀ k
  have hpoint : ‖S.point - center‖ < delta := by simpa only [mem_ball, dist_eq_norm] using hK k hk
  have hpointG : S.point ∈ ball center rG := by
    rw [mem_ball, dist_eq_norm]
    exact hpoint.trans_le (min_le_left _ _)
  have hsmall : A * ‖S.point - center‖ < min radius rH := by
    have he := hpoint.trans_le (min_le_right _ _)
    have hb := (lt_div_iff₀ (by linarith : 0 < A + 1)).mp he
    nlinarith [norm_nonneg (S.point - center)]
  have hpointR : ‖S.point - center‖ < min radius rH := by
    have he := mul_le_mul_of_nonneg_right hA (norm_nonneg (S.point - center))
    nlinarith
  have hpointH : S.point ∈ ball center rH := by
    rw [mem_ball, dist_eq_norm]
    exact hpointR.trans_le (min_le_right _ _)
  have hgrad : ‖S.gradient‖ ≤ (L : ℝ) * ‖S.point - center‖ := by
    rw [hc.2.1]
    exact local_gradient_norm_bound G center rG hrG L hLip hzero S.point hpointG
  have hc₁S : 0 < S.descentConstant := by rw [hc.2.2.1]; exact hc₁
  have hc₂S : S.descentConstant ≤ S.normConstant := by rw [hc.2.2.1, hc.2.2.2]; exact hc₂
  have hfirst := first_probe_distance model S center L L.coe_nonneg hc₁S hc₂S hgrad
  rw [hc.2.2.2] at hfirst
  change ‖S.point + (model S).safeDirection S - center‖ ≤ A * ‖S.point - center‖ at hfirst
  have hrelated := outerSearch_gradientRelated model f G P.armijo S hc₁S hc₂S
  have haccepted := safeguarded_trial_distance center S.point S.gradient R.direction
    S.descentConstant S.normConstant L R.length L.coe_nonneg (hc₁S.trans_le hc₂S).le hgrad hrelated
    (outerSearch_length_pos model f G P.armijo S).le (outerSearch_length_le_one model f G P.armijo S)
  rw [hc.2.2.2] at haccepted
  change ‖S.point + R.length • R.direction - center‖ ≤ A * ‖S.point - center‖ at haccepted
  have hgtrue : G S.point ≠ 0 := local_gradient_ne_zero G H (H center) center rH hrH epsilon mu
    hlocalG hlocalH hpositive (by change mu / 2 < mu; linarith) hzero S.point hpointH (hne k)
  have hgne : S.gradient ≠ 0 := by rwa [hc.2.1]
  have hstep : R.length • R.direction ≠ 0 := gradientRelated_step_ne_zero S.descentConstant S.normConstant
    hc₁S S.gradient R.direction hgne hrelated R.length (outerSearch_length_pos model f G P.armijo S)
  refine ⟨hgne, ⟨hpointR.trans_le (min_le_left _ _), (hfirst.trans_lt hsmall).trans_le (min_le_left _ _)⟩,
    ⟨hpointR.trans_le (min_le_left _ _), (haccepted.trans_lt hsmall).trans_le (min_le_left _ _)⟩, ?_⟩
  exact observedTrialPair_positive_local f G H (H center) center rH epsilon mu hlocalG hlocalH hpositive
    (by change mu / 2 < mu; linarith) S hc.2.1 _ hstep hpointH
    (by rw [mem_ball, dist_eq_norm]; exact (haccepted.trans_lt hsmall).trans_le (min_le_right _ _))

end
end krylov.XR
