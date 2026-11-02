import krylov.XR.CorrectedPairBounds
import krylov.XR.LocalMemory

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

/-- The scalar value term is small whenever its real endpoints and current
anchor are close, uniformly over all lengths of positive observed steps. -/
theorem pair_value_radius_bound {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a : PairObservation E) (x center : E) (r mu upper L : ℝ)
    (hmu : 0 < mu) (hupper : 0 ≤ upper) (hL : 0 ≤ L) (_hr : 0 ≤ r)
    (hs : a.step ≠ 0) (hphi : a.anchorPairing = inner ℝ a.image (x - a.anchor))
    (hcoerc : mu * ‖a.step‖ ^ 2 ≤ inner ℝ a.step a.image)
    (hy : ‖a.image‖ ≤ upper * ‖a.step‖) (hdelta : |a.valueDefect| ≤ L * ‖a.step‖ ^ 3 / 2)
    (ha : ‖a.anchor - center‖ ≤ r) (hb : ‖a.anchor + a.step - center‖ ≤ r) (hx : ‖x - center‖ ≤ r) :
    |12 * (a.anchorPairing / inner ℝ a.step a.image - 1 / 2) * a.valueDefect| ≤
      (6 * L * (2 * upper / mu + 1) * r) * ‖a.step‖ ^ 2 := by
  have hd : ‖x - a.anchor‖ ≤ 2 * r := by
    have hh := norm_sub_le (x - center) (a.anchor - center)
    rw [sub_sub_sub_cancel_right] at hh
    linarith
  have hstep : ‖a.step‖ ≤ 2 * r := by
    have hh := norm_sub_le (a.anchor + a.step - center) (a.anchor - center)
    have he : (a.anchor + a.step - center) - (a.anchor - center) = a.step := by abel
    rw [he] at hh
    linarith
  have hh := pair_value_term_bound a x mu upper L hmu hupper hL hs hphi hcoerc hy hdelta
  have hc : upper / mu * ‖x - a.anchor‖ + ‖a.step‖ / 2 ≤ (2 * upper / mu + 1) * r := by
    have hm := mul_le_mul_of_nonneg_left hd (div_nonneg hupper hmu.le)
    calc
      _ ≤ upper / mu * (2 * r) + (2 * r) / 2 :=
        add_le_add hm (div_le_div_of_nonneg_right hstep (by norm_num))
      _ = _ := by ring
  exact hh.trans (mul_le_mul_of_nonneg_right
    (by nlinarith [mul_le_mul_of_nonneg_left hc (mul_nonneg (by norm_num : (0 : ℝ) ≤ 6) hL)]) (sq_nonneg _))

/-- Every actual cached value term tends to zero in the only relevant
normalized units. In particular the original oversized-term gate will
eventually retain it exactly. -/
theorem algorithmRun_eventually_value_terms (P : Parameters) (hP : P.Valid n)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (x₀ center : EuclideanSpace ℝ (Fin n)) (bounds : SpectralBounds)
    (hF : ∀ᶠ z in 𝓝 center, HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ᶠ z in 𝓝 center, HasFDerivAt G (H z) z) (hH : ContinuousAt H center)
    (radius : ℝ) (hradius : 0 < radius) (L : ℝ≥0)
    (hLip : LipschitzOnWith L H (ball center radius))
    (mu : ℝ) (hmu : 0 < mu) (hpositive : ∀ v, mu * ‖v‖ ^ 2 ≤ inner ℝ v (H center v))
    (hconv : Tendsto (fun k => (algorithmRun P f G x₀ bounds k).point) atTop (𝓝 center))
    (hne : ∀ k, (algorithmRun P f G x₀ bounds k).point ≠ center)
    (budget : ℝ) (hbudget : 0 < budget) :
    ∃ K, ∀ k, K ≤ k →
      ∀ a ∈ (algorithmRun P f G x₀ bounds k).pairs,
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
  obtain ⟨K₁, hK₁⟩ := algorithmRun_eventually_secant_errors P hP f G H x₀ center bounds
    hF hG hH mu hmu hpositive hconv hne epsilon hepsilon
  obtain ⟨K₂, hK₂⟩ := algorithmRun_eventually_local_pairs P hP f G H x₀ center bounds
    hF hG hH mu hmu hpositive hconv hne r hr
  obtain ⟨K₃, hK₃⟩ := Filter.eventually_atTop.mp (hconv.eventually (ball_mem_nhds center hr))
  refine ⟨max K₁ (max K₂ K₃), ?_⟩
  intro k hk a ha
  let S := algorithmRun P f G x₀ bounds k
  have herror := hK₁ k (by omega) a ha
  change ‖a.image - H center a.step‖ ≤ min (mu / 2) 1 * ‖a.step‖ at herror
  have hnear := hK₂ k (by omega) a ha
  have hfaithful := algorithmRun_pairs_faithful P f G x₀ bounds k a ha
  have hs := positivePair_step_ne_zero a (algorithmRun_pairs_positive P f G x₀ bounds k a ha)
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

end
end krylov.XR
