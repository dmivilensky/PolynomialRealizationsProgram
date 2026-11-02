import krylov.XR.EuclideanPracticalLocal
import krylov.XR.EuclideanSourceGate

/-!
# Actual Euclidean value gates for practical XR-F

Article: Corollary 7.4 [cor:xrF] of krylov.tex.
Finite forgetting localizes actual endpoint records. The existing Euclidean
split bounds derive small normalized terms and both selected-model gates.
-/
namespace krylov.XR
noncomputable section
open Set Metric Filter Topology
open scoped InnerProductSpace NNReal
variable {n : ℕ}
set_option maxHeartbeats 800000

/-- Every actual cached value term tends to zero in the only relevant
normalized units. In particular the original oversized-term gate will
eventually retain it exactly. -/
theorem euclideanPracticalRun_eventually_value_terms (P : Parameters) (hP : P.Valid n)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (x₀ center : EuclideanSpace ℝ (Fin n))
    (hF : ∀ᶠ z in 𝓝 center, HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ᶠ z in 𝓝 center, HasFDerivAt G (H z) z) (hH : ContinuousAt H center)
    (radius : ℝ) (hradius : 0 < radius) (L : ℝ≥0)
    (hLip : LipschitzOnWith L H (ball center radius))
    (mu : ℝ) (hmu : 0 < mu) (hpositive : ∀ v, mu * ‖v‖ ^ 2 ≤ inner ℝ v (H center v))
    (hconv : Tendsto (fun k => (euclideanPracticalRun P f G x₀ k).point) atTop (𝓝 center))
    (hne : ∀ k, (euclideanPracticalRun P f G x₀ k).point ≠ center)
    (budget : ℝ) (hbudget : 0 < budget) :
    ∃ K, ∀ k, K ≤ k →
      ∀ a ∈ (euclideanPracticalRun P f G x₀ k).pairs,
        (mu / 2) * ‖a.step‖ ^ 2 ≤ inner ℝ a.step a.image ∧
        |12 * (inner ℝ a.step ((euclideanPracticalRun P f G x₀ k).point - a.anchor) / ‖a.step‖ ^ 2 - 1 / 2) * a.valueDefect| ≤
          min budget (mu / 4) * ‖a.step‖ ^ 2 := by
  obtain ⟨r₀, hr₀, hlocal⟩ := Metric.eventually_nhds_iff.mp (hF.and hG)
  let sourceRadius := min radius r₀
  have hsource : 0 < sourceRadius := lt_min hradius hr₀
  let C := 18 * (L : ℝ)
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
  obtain ⟨K₁, hK₁⟩ := euclideanPracticalRun_eventually_secant_errors P hP f G H x₀ center
    hF hG hH mu hmu hpositive hconv hne epsilon hepsilon
  obtain ⟨K₂, hK₂⟩ := euclideanPracticalRun_eventually_local_pairs P hP f G H x₀ center
    hF hG hH mu hmu hpositive hconv hne r hr
  obtain ⟨K₃, hK₃⟩ := Filter.eventually_atTop.mp (hconv.eventually (ball_mem_nhds center hr))
  refine ⟨max K₁ (max K₂ K₃), ?_⟩
  intro k hk a ha
  let S := euclideanPracticalRun P f G x₀ k
  have herror := hK₁ k (by omega) a ha
  change ‖a.image - H center a.step‖ ≤ min (mu / 2) 1 * ‖a.step‖ at herror
  have hnear := hK₂ k (by omega) a ha
  have hfaithful := euclideanPracticalRun_pairs_faithful P f G x₀ k a ha
  have hs := positivePair_step_ne_zero a (euclideanPracticalRun_pairs_positive P f G x₀ k a ha)
  have hcoerc : (mu / 2) * ‖a.step‖ ^ 2 ≤ inner ℝ a.step a.image := by
    have hh := (abs_real_inner_le_norm a.step (a.image - H center a.step)).trans
      (mul_le_mul_of_nonneg_left herror (norm_nonneg _))
    rw [inner_sub_right] at hh
    have hb := (abs_le.mp hh).1
    have hm := mul_le_mul_of_nonneg_right (min_le_left (mu / 2) 1) (sq_nonneg ‖a.step‖)
    nlinarith [hpositive a.step]
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
  have hd : ‖S.point - a.anchor‖ ≤ 2 * r := by
    have hh := norm_sub_le (S.point - center) (a.anchor - center)
    rw [sub_sub_sub_cancel_right] at hh
    linarith [hnear.1.le]
  have hstep : ‖a.step‖ ≤ 2 * r := by
    have hh := norm_sub_le (a.anchor + a.step - center) (a.anchor - center)
    have he : (a.anchor + a.step - center) - (a.anchor - center) = a.step := by abel
    rw [he] at hh
    linarith [hnear.1.le, hnear.2.le]
  have hv := pair_euclidean_value_term_bound a S.point (L : ℝ) L.coe_nonneg hs hdelta
  have hv' : |12 * (inner ℝ a.step (S.point - a.anchor) / ‖a.step‖ ^ 2 - 1 / 2) * a.valueDefect| ≤
      (C * r) * ‖a.step‖ ^ 2 := by
    apply hv.trans
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    dsimp only [C]
    nlinarith [mul_le_mul_of_nonneg_left hd L.coe_nonneg,
      mul_le_mul_of_nonneg_left hstep L.coe_nonneg]
  refine ⟨hcoerc, hv'.trans ?_⟩
  exact mul_le_mul_of_nonneg_right hsmall (sq_nonneg _)

end
end krylov.XR


namespace krylov.XR
noncomputable section
open Set Metric Filter Topology krylov.Methods
open scoped InnerProductSpace NNReal Matrix.Norms.L2Operator
variable {n : ℕ}

/-- Primitive G1 source yields both the actual scalar gates and complete
normalized corrected-model approximation on every late real ModelStep. -/
theorem euclideanPracticalRun_eventually_corrected_data (P : Parameters) (hP : P.Valid n)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (x₀ center : EuclideanSpace ℝ (Fin n))
    (hF : ∀ᶠ z in 𝓝 center, HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ᶠ z in 𝓝 center, HasFDerivAt G (H z) z) (hH : ContinuousAt H center)
    (radius : ℝ) (hradius : 0 < radius) (L : ℝ≥0)
    (hLip : LipschitzOnWith L H (ball center radius))
    (mu : ℝ) (hmu : 0 < mu) (hpositive : ∀ v, mu * ‖v‖ ^ 2 ≤ inner ℝ v (H center v))
    (hconv : Tendsto (fun k => (euclideanPracticalRun P f G x₀ k).point) atTop (𝓝 center))
    (hne : ∀ k, (euclideanPracticalRun P f G x₀ k).point ≠ center)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ K, ∀ k, K ≤ k →
      let W := (euclideanPracticalModel P (euclideanPracticalRun P f G x₀ k)).pairs
      (∀ i : Fin W.length, ‖storedImages W i - H center (storedSteps W i)‖ ≤
        epsilon * ‖storedSteps W i‖) ∧
      (∀ i : Fin W.length, |12 * euclideanStoredSplit (euclideanPracticalRun P f G x₀ k).point W i * (W.get i).valueDefect| ≤ storedPairing W i i / 2) ∧
      ‖rescaleModel (euclideanStoredValueModel (euclideanPracticalRun P f G x₀ k).point W) (fun i => ‖storedSteps W i‖⁻¹) -
        localReferenceGram (H center) (krylov.Convergence.unitWindow (storedSteps W))‖ ≤
          (W.length : ℝ) * epsilon := by
  let e : ℝ≥0 := ⟨epsilon / 2, by positivity⟩
  have he : 0 < (e : ℝ) := by change 0 < epsilon / 2; positivity
  obtain ⟨K₁, hK₁⟩ := euclideanPracticalRun_eventually_secant_errors P hP f G H x₀ center
    hF hG hH mu hmu hpositive hconv hne e he
  obtain ⟨K₂, hK₂⟩ := euclideanPracticalRun_eventually_value_terms P hP f G H x₀ center
    hF hG hH radius hradius L hLip mu hmu hpositive hconv hne (epsilon / 2) (by positivity)
  have hsym := local_hessian_symmetric f G H center hF hG.self_of_nhds
  refine ⟨max K₁ K₂, ?_⟩
  intro k hk
  let S := euclideanPracticalRun P f G x₀ k
  let W := (euclideanPracticalModel P S).pairs
  have hs (i : Fin W.length) : storedSteps W i ≠ 0 :=
    positivePair_step_ne_zero _ (euclideanPracticalRun_pairs_positive P f G x₀ k _
      (euclideanPracticalModel_pair_mem P S _ (List.get_mem _ i)))
  have hy (i : Fin W.length) : ‖storedImages W i - H center (storedSteps W i)‖ ≤
      epsilon / 2 * ‖storedSteps W i‖ :=
    hK₁ k (by omega) _ (euclideanPracticalModel_pair_mem P S _ (List.get_mem _ i))
  have hv (i : Fin W.length) := hK₂ k (by omega) _ (euclideanPracticalModel_pair_mem P S _ (List.get_mem W i))
  have hscalar (i : Fin W.length) :
      |12 * euclideanStoredSplit (euclideanPracticalRun P f G x₀ k).point W i * (W.get i).valueDefect| ≤ epsilon / 2 * ‖storedSteps W i‖ ^ 2 := by
    exact (hv i).2.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg _))
  have hgate (i : Fin W.length) :
      |12 * euclideanStoredSplit (euclideanPracticalRun P f G x₀ k).point W i * (W.get i).valueDefect| ≤ storedPairing W i i / 2 := by
    have hb := (hv i).2.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) (sq_nonneg _))
    have hc := (hv i).1
    change (mu / 2) * ‖storedSteps W i‖ ^ 2 ≤ storedPairing W i i at hc
    change |12 * euclideanStoredSplit (euclideanPracticalRun P f G x₀ k).point W i * (W.get i).valueDefect| ≤ (mu / 4) * ‖storedSteps W i‖ ^ 2 at hb
    nlinarith
  have hmodel := euclideanStoredValueModel_normalized_error S.point (H center) hsym W hs (epsilon / 2) (epsilon / 2)
    (by positivity) (by positivity) hy (fun i => (euclideanStoredValueTerm_abs_le S.point W i).trans (hscalar i))
  refine ⟨?_, hgate, ?_⟩
  · intro i
    exact (hy i).trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))
  · simpa only [show epsilon / 2 + epsilon / 2 = epsilon by ring] using hmodel

end
end krylov.XR


namespace krylov.XR
noncomputable section
open Set Metric Filter Topology krylov.Methods
open scoped InnerProductSpace NNReal Matrix.Norms.L2Operator
variable {n : ℕ}

/-- On every sufficiently late actual first ModelStep with F enabled,
the true scalar terms and the corrected Hermitian gate all pass. -/
theorem euclideanPracticalRun_eventually_corrected_gates (P : Parameters) (hP : P.Valid n)
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
    (hconv : Tendsto (fun k => (euclideanPracticalRun P f G x₀ k).point) atTop (𝓝 center))
    (hne : ∀ k, (euclideanPracticalRun P f G x₀ k).point ≠ center)
    (K₀ : ℕ)
    (hgain : ∀ k, K₀ ≤ k →
      let W := incomingWindow (euclideanPracticalRun P f G x₀ k)
      ∀ w : Fin W.length → ℝ, sigma ^ 2 * ‖WithLp.toLp 2 w‖ ^ 2 ≤
        ‖combine (krylov.Convergence.unitWindow (storedSteps W)) w‖ ^ 2) :
    ∃ K, ∀ k, K ≤ k →
      let W := (euclideanPracticalModel P (euclideanPracticalRun P f G x₀ k)).pairs
      (∀ i : Fin W.length, |12 * euclideanStoredSplit (euclideanPracticalRun P f G x₀ k).point W i * (W.get i).valueDefect| ≤ storedPairing W i i / 2) ∧
        euclideanCorrectedWindowPasses P.windowThreshold (euclideanPracticalRun P f G x₀ k).point W ∧ selectedEuclideanModel P (euclideanPracticalRun P f G x₀ k).point W = euclideanStoredValueModel (euclideanPracticalRun P f G x₀ k).point W := by
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
  obtain ⟨K₁, hK₁⟩ := euclideanPracticalRun_eventually_corrected_data P hP f G H x₀ center hF hG hH
    radius hradius L hLip mu hmu hpositive hconv hne epsilon hepsilon
  obtain ⟨K₂, hK₂⟩ := euclideanPracticalRun_eventually_retains_window P hP f G H x₀ center hF hG hH
    mu sigma hmu hsigma hpositive hconv hne K₀ hgain
  have hsym := local_hessian_symmetric f G H center hF hG.self_of_nhds
  refine ⟨max K₀ (max K₁ K₂), ?_⟩
  intro k hk
  let S := euclideanPracticalRun P f G x₀ k
  let W := (euclideanPracticalModel P S).pairs
  have hdata := hK₁ k (by omega)
  have hret : W = incomingWindow S := (hK₂ k (by omega)).2.1
  have hlen : W.length ≤ n := (euclideanPracticalModel_length_le P S).trans (min_le_right _ _)
  have hlenR : (W.length : ℝ) ≤ n := by exact_mod_cast hlen
  have hs (i : Fin W.length) : storedSteps W i ≠ 0 :=
    positivePair_step_ne_zero _ (euclideanPracticalRun_pairs_positive P f G x₀ k _
      (euclideanPracticalModel_pair_mem P S _ (List.get_mem _ i)))
  have hgain : ∀ w : Fin W.length → ℝ, sigma ^ 2 * ‖WithLp.toLp 2 w‖ ^ 2 ≤
      ‖combine (krylov.Convergence.unitWindow (storedSteps W)) w‖ ^ 2 := by
    rw [hret]
    exact hgain k (by omega)
  have hpass := euclideanCorrectedWindowPasses_of_errors P.windowThreshold htheta S.point (H center) hsym W hs
    mu sigma epsilon hmu hsigma hepsilon.le hpositive hgain hdata.1 hdata.2.2
    ((mul_le_mul_of_nonneg_right hlenR hepsilon.le).trans hsmall)
    ((div_le_div_of_nonneg_right (by nlinarith [mul_le_mul_of_nonneg_right hlenR hepsilon.le])
      hcoerc.le).trans_lt hgate)
  exact ⟨hdata.2.1, hpass, ite_eq_left ⟨hon, hpass⟩⟩

end
end krylov.XR
