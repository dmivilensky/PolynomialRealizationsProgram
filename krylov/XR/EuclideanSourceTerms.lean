import krylov.XR.EuclideanPairBounds
import krylov.XR.EuclideanLocalMemory

/-!
Article: main_krylov, cor:xrF and apH:impl, source-derived value gates.
Use: the original Lipschitz-Hessian G1 source makes every genuinely
cached value correction small in squared-step units. No lower bound on
individual step lengths, split bound, gate success or query enclosure is
assumed. Source: finite actual memory forgetting and genuine cubic defects.
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
theorem euclideanAlgorithmRun_eventually_value_terms (P : Parameters) (hP : P.Valid n)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (x₀ center : EuclideanSpace ℝ (Fin n)) (bounds : SpectralBounds)
    (hF : ∀ᶠ z in 𝓝 center, HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ᶠ z in 𝓝 center, HasFDerivAt G (H z) z) (hH : ContinuousAt H center)
    (radius : ℝ) (hradius : 0 < radius) (L : ℝ≥0)
    (hLip : LipschitzOnWith L H (ball center radius))
    (mu : ℝ) (hmu : 0 < mu) (hpositive : ∀ v, mu * ‖v‖ ^ 2 ≤ inner ℝ v (H center v))
    (hconv : Tendsto (fun k => (euclideanAlgorithmRun P f G x₀ bounds k).point) atTop (𝓝 center))
    (hne : ∀ k, (euclideanAlgorithmRun P f G x₀ bounds k).point ≠ center)
    (budget : ℝ) (hbudget : 0 < budget) :
    ∃ K, ∀ k, K ≤ k →
      ∀ a ∈ (euclideanAlgorithmRun P f G x₀ bounds k).pairs,
        (mu / 2) * ‖a.step‖ ^ 2 ≤ inner ℝ a.step a.image ∧
        |12 * (inner ℝ a.step ((euclideanAlgorithmRun P f G x₀ bounds k).point - a.anchor) / ‖a.step‖ ^ 2 - 1 / 2) * a.valueDefect| ≤
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
  obtain ⟨K₁, hK₁⟩ := euclideanAlgorithmRun_eventually_secant_errors P hP f G H x₀ center bounds
    hF hG hH mu hmu hpositive hconv hne epsilon hepsilon
  obtain ⟨K₂, hK₂⟩ := euclideanAlgorithmRun_eventually_local_pairs P hP f G H x₀ center bounds
    hF hG hH mu hmu hpositive hconv hne r hr
  obtain ⟨K₃, hK₃⟩ := Filter.eventually_atTop.mp (hconv.eventually (ball_mem_nhds center hr))
  refine ⟨max K₁ (max K₂ K₃), ?_⟩
  intro k hk a ha
  let S := euclideanAlgorithmRun P f G x₀ bounds k
  have herror := hK₁ k (by omega) a ha
  change ‖a.image - H center a.step‖ ≤ min (mu / 2) 1 * ‖a.step‖ at herror
  have hnear := hK₂ k (by omega) a ha
  have hfaithful := euclideanAlgorithmRun_pairs_faithful P f G x₀ bounds k a ha
  have hs := positivePair_step_ne_zero a (euclideanAlgorithmRun_pairs_positive P f G x₀ bounds k a ha)
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
