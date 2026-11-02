import krylov.XR.PracticalGrowthLocal

/-!
# Eventual value-model gates on the practical execution

Article Corollary 7.4 (`cor:xrF`). These are compositions of the actual
finite-memory locality theorem with the policy-independent endpoint-value
bounds. Neither a size-gate decision nor a corrected-model error is assumed.
-/
namespace krylov.XR
noncomputable section
open Set Metric Filter Topology krylov.Methods
open scoped InnerProductSpace NNReal Matrix.Norms.L2Operator
variable {n : ℕ}
set_option maxHeartbeats 800000

/-- Every actual cached value term tends to zero in the only relevant
normalized units. In particular the original oversized-term gate will
eventually retain it exactly. -/
theorem practicalRun_eventually_value_terms (P : Parameters) (hP : P.Valid n)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (x₀ center : EuclideanSpace ℝ (Fin n))
    (hF : ∀ᶠ z in 𝓝 center, HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ᶠ z in 𝓝 center, HasFDerivAt G (H z) z) (hH : ContinuousAt H center)
    (radius : ℝ) (hradius : 0 < radius) (L : ℝ≥0)
    (hLip : LipschitzOnWith L H (ball center radius))
    (mu : ℝ) (hmu : 0 < mu) (hpositive : ∀ v, mu * ‖v‖ ^ 2 ≤ inner ℝ v (H center v))
    (hconv : Tendsto (fun k => (practicalRun P f G x₀ k).point) atTop (𝓝 center))
    (hne : ∀ k, (practicalRun P f G x₀ k).point ≠ center)
    (budget : ℝ) (hbudget : 0 < budget) :
    ∃ K, ∀ k, K ≤ k →
      ∀ a ∈ (practicalRun P f G x₀ k).pairs,
        (mu / 2) * ‖a.step‖ ^ 2 ≤ inner ℝ a.step a.image ∧
        |12 * (a.anchorPairing / inner ℝ a.step a.image - 1 / 2) * a.valueDefect| ≤
          min budget (mu / 4) * ‖a.step‖ ^ 2 := by
  obtain ⟨r₀, hr₀, hlocal⟩ := Metric.eventually_nhds_iff.mp (hF.and hG)
  let sourceRadius := min radius r₀
  have hsource : 0 < sourceRadius := lt_min hradius hr₀
  let upper := ‖H center‖ + 1
  have hupper : 0 < upper := by dsimp only [upper]; positivity
  let C := 6 * (L : ℝ) * (2 * upper / (mu / 2) + 1)
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  let r := min sourceRadius (min budget (mu / 4) / (C + 1))
  have hr : 0 < r := lt_min hsource (div_pos (lt_min hbudget (by positivity)) (by positivity))
  have hrsource : r ≤ sourceRadius := min_le_left _ _
  have hsmall : C * r ≤ min budget (mu / 4) := by
    have hh := (le_div_iff₀ (by positivity : 0 < C + 1)).mp (min_le_right sourceRadius
      (min budget (mu / 4) / (C + 1)))
    change r * (C + 1) ≤ _ at hh
    nlinarith
  let epsilon : ℝ≥0 := ⟨min (mu / 2) 1, by positivity⟩
  have hepsilon : 0 < (epsilon : ℝ) := lt_min (by positivity) (by norm_num)
  obtain ⟨K₁, hK₁⟩ := practicalRun_eventually_secant_errors P hP f G H x₀ center
    hF hG hH mu hmu hpositive hconv hne epsilon hepsilon
  obtain ⟨K₂, hK₂⟩ := practicalRun_eventually_local_pairs P hP f G H x₀ center
    hF hG hH mu hmu hpositive hconv hne r hr
  obtain ⟨K₃, hK₃⟩ := Filter.eventually_atTop.mp (hconv.eventually (ball_mem_nhds center hr))
  refine ⟨max K₁ (max K₂ K₃), ?_⟩
  intro k hk a ha
  let S := practicalRun P f G x₀ k
  have herror := hK₁ k (by omega) a ha
  change ‖a.image - H center a.step‖ ≤ min (mu / 2) 1 * ‖a.step‖ at herror
  have hnear := hK₂ k (by omega) a ha
  have hfaithful := practicalRun_pairs_faithful P f G x₀ k a ha
  have hs := positivePair_step_ne_zero a (practicalRun_pairs_positive P f G x₀ k a ha)
  have hcoerc : (mu / 2) * ‖a.step‖ ^ 2 ≤ inner ℝ a.step a.image := by
    have hh := (abs_real_inner_le_norm a.step (a.image - H center a.step)).trans
      (mul_le_mul_of_nonneg_left herror (norm_nonneg _))
    rw [inner_sub_right] at hh
    have hb := (abs_le.mp hh).1
    have hm := mul_le_mul_of_nonneg_right (min_le_left (mu / 2) 1) (sq_nonneg ‖a.step‖)
    nlinarith [hpositive a.step]
  have hy : ‖a.image‖ ≤ upper * ‖a.step‖ := by
    have htri : ‖a.image‖ ≤ ‖a.image - H center a.step‖ + ‖H center a.step‖ :=
      norm_le_norm_sub_add a.image (H center a.step)
    have hm := mul_le_mul_of_nonneg_right (min_le_right (mu / 2) 1) (norm_nonneg a.step)
    dsimp only [upper]
    nlinarith [htri, (H center).le_opNorm a.step]
  have haS : a.anchor ∈ ball center sourceRadius := by
    rw [mem_ball, dist_eq_norm]
    exact hnear.1.trans_le hrsource
  have hbS : a.anchor + a.step ∈ ball center sourceRadius := by
    rw [mem_ball, dist_eq_norm]
    exact hnear.2.trans_le hrsource
  have hdelta : |a.valueDefect| ≤ (L : ℝ) * ‖a.step‖ ^ 3 / 2 := by
    rw [hfaithful.valueDefect_eq]
    apply segmentValueDefect_on_lipschitz_set f G H (ball center sourceRadius)
      (convex_ball _ _) L (hLip.mono (ball_subset_ball (min_le_left _ _)))
    · intro z hz
      exact (hlocal ((ball_subset_ball (min_le_right _ _)) hz)).1
    · intro z hz
      exact (hlocal ((ball_subset_ball (min_le_right _ _)) hz)).2
    · exact haS
    · exact hbS
  have hx : ‖S.point - center‖ ≤ r := by
    have hh := hK₃ k (by omega)
    exact (show ‖S.point - center‖ < r by exact hh).le
  have hv := pair_value_radius_bound a S.point center r (mu / 2) upper L (by positivity)
    hupper.le L.coe_nonneg hr.le hs hfaithful.2.2 hcoerc hy hdelta hnear.1.le hnear.2.le hx
  refine ⟨hcoerc, hv.trans ?_⟩
  exact mul_le_mul_of_nonneg_right hsmall (sq_nonneg _)


/-- Primitive G1 source yields both the actual scalar gates and complete
normalized corrected-model approximation on every late real ModelStep. -/
theorem practicalRun_eventually_corrected_data (P : Parameters) (hP : P.Valid n)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (x₀ center : EuclideanSpace ℝ (Fin n))
    (hF : ∀ᶠ z in 𝓝 center, HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ᶠ z in 𝓝 center, HasFDerivAt G (H z) z) (hH : ContinuousAt H center)
    (radius : ℝ) (hradius : 0 < radius) (L : ℝ≥0)
    (hLip : LipschitzOnWith L H (ball center radius))
    (mu : ℝ) (hmu : 0 < mu) (hpositive : ∀ v, mu * ‖v‖ ^ 2 ≤ inner ℝ v (H center v))
    (hconv : Tendsto (fun k => (practicalRun P f G x₀ k).point) atTop (𝓝 center))
    (hne : ∀ k, (practicalRun P f G x₀ k).point ≠ center)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ K, ∀ k, K ≤ k →
      let W := (practicalModel P (practicalRun P f G x₀ k)).pairs
      (∀ i : Fin W.length, ‖storedImages W i - H center (storedSteps W i)‖ ≤
        epsilon * ‖storedSteps W i‖) ∧
      (∀ i : Fin W.length, |12 * storedSplit W i * (W.get i).valueDefect| ≤ storedPairing W i i / 2) ∧
      ‖rescaleModel (storedValueModel W) (fun i => ‖storedSteps W i‖⁻¹) -
        localReferenceGram (H center) (krylov.Convergence.unitWindow (storedSteps W))‖ ≤
          (W.length : ℝ) * epsilon := by
  let e : ℝ≥0 := ⟨epsilon / 2, by positivity⟩
  have he : 0 < (e : ℝ) := by change 0 < epsilon / 2; positivity
  obtain ⟨K₁, hK₁⟩ := practicalRun_eventually_secant_errors P hP f G H x₀ center
    hF hG hH mu hmu hpositive hconv hne e he
  obtain ⟨K₂, hK₂⟩ := practicalRun_eventually_value_terms P hP f G H x₀ center
    hF hG hH radius hradius L hLip mu hmu hpositive hconv hne (epsilon / 2) (by positivity)
  have hsym := local_hessian_symmetric f G H center hF hG.self_of_nhds
  refine ⟨max K₁ K₂, ?_⟩
  intro k hk
  let S := practicalRun P f G x₀ k
  let W := (practicalModel P S).pairs
  have hs (i : Fin W.length) : storedSteps W i ≠ 0 :=
    positivePair_step_ne_zero _ (practicalRun_pairs_positive P f G x₀ k _
      (practicalModel_pair_mem P S _ (List.get_mem _ i)))
  have hy (i : Fin W.length) : ‖storedImages W i - H center (storedSteps W i)‖ ≤
      epsilon / 2 * ‖storedSteps W i‖ :=
    hK₁ k (by omega) _ (practicalModel_pair_mem P S _ (List.get_mem _ i))
  have hv (i : Fin W.length) := hK₂ k (by omega) _ (practicalModel_pair_mem P S _ (List.get_mem W i))
  have hscalar (i : Fin W.length) :
      |12 * storedSplit W i * (W.get i).valueDefect| ≤ epsilon / 2 * ‖storedSteps W i‖ ^ 2 := by
    exact (hv i).2.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg _))
  have hgate (i : Fin W.length) :
      |12 * storedSplit W i * (W.get i).valueDefect| ≤ storedPairing W i i / 2 := by
    have hb := (hv i).2.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) (sq_nonneg _))
    have hc := (hv i).1
    change (mu / 2) * ‖storedSteps W i‖ ^ 2 ≤ storedPairing W i i at hc
    change |12 * storedSplit W i * (W.get i).valueDefect| ≤ (mu / 4) * ‖storedSteps W i‖ ^ 2 at hb
    nlinarith
  have hmodel := storedValueModel_normalized_error (H center) hsym W hs (epsilon / 2) (epsilon / 2)
    (by positivity) (by positivity) hy (fun i => (storedValueTerm_abs_le W i).trans (hscalar i))
  refine ⟨?_, hgate, ?_⟩
  · intro i
    exact (hy i).trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))
  · simpa only [show epsilon / 2 + epsilon / 2 = epsilon by ring] using hmodel


/-- On every sufficiently late actual first ModelStep with F enabled,
the true scalar terms and the corrected Hermitian gate all pass. -/
theorem practicalRun_eventually_corrected_gates (P : Parameters) (hP : P.Valid n)
    (hon : P.valuesEnabled = true)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (x₀ center : EuclideanSpace ℝ (Fin n))
    (hF : ∀ᶠ z in 𝓝 center, HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ᶠ z in 𝓝 center, HasFDerivAt G (H z) z) (hH : ContinuousAt H center)
    (radius : ℝ) (hradius : 0 < radius) (L : ℝ≥0)
    (hLip : LipschitzOnWith L H (ball center radius))
    (mu sigma : ℝ) (hmu : 0 < mu) (hsigma : 0 < sigma)
    (hpositive : ∀ v, mu * ‖v‖ ^ 2 ≤ inner ℝ v (H center v))
    (hconv : Tendsto (fun k => (practicalRun P f G x₀ k).point) atTop (𝓝 center))
    (hne : ∀ k, (practicalRun P f G x₀ k).point ≠ center)
    (K₀ : ℕ)
    (hgain : ∀ k, K₀ ≤ k →
      let W := incomingWindow (practicalRun P f G x₀ k)
      ∀ w : Fin W.length → ℝ, sigma ^ 2 * ‖WithLp.toLp 2 w‖ ^ 2 ≤
        ‖combine (krylov.Convergence.unitWindow (storedSteps W)) w‖ ^ 2) :
    ∃ K, ∀ k, K ≤ k →
      let W := (practicalModel P (practicalRun P f G x₀ k)).pairs
      (∀ i : Fin W.length, |12 * storedSplit W i * (W.get i).valueDefect| ≤ storedPairing W i i / 2) ∧
        correctedWindowPasses P.windowThreshold W ∧ selectedModel P W = storedValueModel W := by
  have htheta : 0 < P.windowThreshold := hP.2.2.2.2.2.1
  have hcoerc : 0 < localCoercivity mu sigma := by unfold localCoercivity; positivity
  let epsilon : ℝ := min (mu * sigma ^ 2 / (8 * ((n : ℝ) + 1)))
    (P.windowThreshold * localCoercivity mu sigma / (4 * ((n : ℝ) + 1)))
  have hepsilon : 0 < epsilon := by dsimp only [epsilon]; positivity
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
  obtain ⟨K₁, hK₁⟩ := practicalRun_eventually_corrected_data P hP f G H x₀ center hF hG hH
    radius hradius L hLip mu hmu hpositive hconv hne epsilon hepsilon
  obtain ⟨K₂, hK₂⟩ := practicalRun_eventually_retains_window P hP f G H x₀ center hF hG hH
    mu sigma hmu hsigma hpositive hconv hne K₀ hgain
  have hsym := local_hessian_symmetric f G H center hF hG.self_of_nhds
  refine ⟨max K₀ (max K₁ K₂), ?_⟩
  intro k hk
  let S := practicalRun P f G x₀ k
  let W := (practicalModel P S).pairs
  have hdata := hK₁ k (by omega)
  have hret : W = incomingWindow S := (hK₂ k (by omega)).2.1
  have hlen : W.length ≤ n := (practicalModel_length_le P S).trans (min_le_right _ _)
  have hlenR : (W.length : ℝ) ≤ n := by exact_mod_cast hlen
  have hs (i : Fin W.length) : storedSteps W i ≠ 0 :=
    positivePair_step_ne_zero _ (practicalRun_pairs_positive P f G x₀ k _
      (practicalModel_pair_mem P S _ (List.get_mem _ i)))
  have hgain : ∀ w : Fin W.length → ℝ, sigma ^ 2 * ‖WithLp.toLp 2 w‖ ^ 2 ≤
      ‖combine (krylov.Convergence.unitWindow (storedSteps W)) w‖ ^ 2 := by
    rw [hret]
    exact hgain k (by omega)
  have hpass := correctedWindowPasses_of_errors P.windowThreshold htheta (H center) hsym W hs
    mu sigma epsilon hmu hsigma hepsilon.le hpositive hgain hdata.1 hdata.2.2
    ((mul_le_mul_of_nonneg_right hlenR hepsilon.le).trans hsmall)
    ((div_le_div_of_nonneg_right (by nlinarith [mul_le_mul_of_nonneg_right hlenR hepsilon.le])
      hcoerc.le).trans_lt hgate)
  exact ⟨hdata.2.1, hpass, ite_eq_left ⟨hon, hpass⟩⟩

end
end krylov.XR
