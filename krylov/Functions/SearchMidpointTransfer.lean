import krylov.Functions.SearchTrajectory
import krylov.Functions.MidpointExpansion

/-!
Article: main_krylov, lem:cycle-transfer and thm:Htransfer, actual midpoint increments.
Use: derive uniform first-order secant expansions on the genuine adaptive
search executor from its proved query localization and the real derivative of
the Hessian. The midpoint arguments here are the actual queried midpoints.
Source: Appendix G, the proved uniform Frechet/Bochner midpoint expansion.
-/

namespace krylov.Functions
noncomputable section
open Set Metric chebyshev1.Nonlinear
open scoped InnerProductSpace NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- All genuine search secants have the same uniform midpoint little-o bound at the initial scale.
Article: main_krylov, lem:cycle-transfer, actual adaptive search query transfer.
Proof: the original objective sublevel bound encloses both actual endpoints;
convexity encloses the complete segment, so the genuine uniform Hessian
derivative expansion applies with one radius for every history and every index. -/
theorem exactSearchPoint_midpoint_expansion (f : E → ℝ) (G : E → E)
    (H : E → E →L[ℝ] E) (T : E →L[ℝ] E →L[ℝ] E)
    {r : ℝ} (hr : 0 < r) (hG₀ : G 0 = 0) (hH₀ : H 0 = ContinuousLinearMap.id ℝ E)
    {L : ℝ≥0} (hLr : (L : ℝ) * r ≤ 1 / 2)
    (hH : LipschitzOnWith L H (closedBall 0 r))
    (hF : ∀ z ∈ closedBall (0 : E) r, HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z ∈ closedBall (0 : E) r, HasFDerivAt G (H z) z)
    (hD : HasFDerivAt H T 0) :
    ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧
      ∀ x₀ : E, ‖x₀‖ < δ → ∀ direction : List E → E, ∀ k : ℕ,
      let a := exactSearchPoint f r direction x₀ k
      let s := exactSearchPoint f r direction x₀ (k + 1) - a
      ‖averagedDerivative H a s - H 0 - T (a + (1 / 2 : ℝ) • s)‖ ≤ η * ‖x₀‖ := by
  intro η hη
  have hc : ContinuousOn H (ball 0 r) := hH.continuousOn.mono ball_subset_closedBall
  obtain ⟨ρ, hρ, _, hrem⟩ := averagedHessian_midpoint_expansion H T hr hc hD
    (η / 2) (by positivity)
  refine ⟨min (r / 2) (ρ / 2), lt_min (by positivity) (by positivity), ?_⟩
  intro x₀ hx₀ direction k
  have hx : ‖x₀‖ < r / 2 := hx₀.trans_le (min_le_left _ _)
  have hloc := exactSearchPoint_localization f G H hr hG₀ hH₀ hLr hH hF hG direction x₀ hx
  have hsqrt : Real.sqrt (3 : ℝ) ≤ 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_nonneg (3 : ℝ)]
  have hbound j : ‖exactSearchPoint f r direction x₀ j‖ ≤ 2 * ‖x₀‖ :=
    (hloc j).1.trans (mul_le_mul_of_nonneg_right hsqrt (norm_nonneg _))
  let a := exactSearchPoint f r direction x₀ k
  let s := exactSearchPoint f r direction x₀ (k + 1) - a
  have hseg t (ht : t ∈ Icc (0 : ℝ) 1) : ‖a + t • s‖ ≤ 2 * ‖x₀‖ := by
    have ha : a ∈ closedBall (0 : E) (2 * ‖x₀‖) := by
      simpa only [mem_closedBall, dist_zero_right] using hbound k
    have hb : a + s ∈ closedBall (0 : E) (2 * ‖x₀‖) := by
      simpa only [a, s, add_sub_cancel] using
        (show exactSearchPoint f r direction x₀ (k + 1) ∈ closedBall (0 : E) (2 * ‖x₀‖) by
          simpa only [mem_closedBall, dist_zero_right] using hbound (k + 1))
    have h := (convex_closedBall (0 : E) (2 * ‖x₀‖)).add_smul_mem ha hb ht
    simpa only [mem_closedBall, dist_zero_right] using h
  have hρx : 2 * ‖x₀‖ < ρ := by
    have h := hx₀.trans_le (min_le_right _ _)
    linarith
  have he := hrem (2 * ‖x₀‖) (by positivity) hρx a s hseg
  convert! he using 1
  ring

/-- Actual adjacent search secants differ by the same third-derivative slice at their true midpoint difference.
Article: main_krylov, thm:Htransfer, actual midpoint part of the increment formula.
Proof: subtract the two genuine midpoint expansions and apply the triangle inequality.
Reference-midpoint replacement additionally uses native reference trajectory stability. -/
theorem exactSearchPoint_hessian_increment (f : E → ℝ) (G : E → E)
    (H : E → E →L[ℝ] E) (T : E →L[ℝ] E →L[ℝ] E)
    {r : ℝ} (hr : 0 < r) (hG₀ : G 0 = 0) (hH₀ : H 0 = ContinuousLinearMap.id ℝ E)
    {L : ℝ≥0} (hLr : (L : ℝ) * r ≤ 1 / 2)
    (hH : LipschitzOnWith L H (closedBall 0 r))
    (hF : ∀ z ∈ closedBall (0 : E) r, HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z ∈ closedBall (0 : E) r, HasFDerivAt G (H z) z)
    (hD : HasFDerivAt H T 0) :
    ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧
      ∀ x₀ : E, ‖x₀‖ < δ → ∀ direction : List E → E, ∀ k : ℕ,
      let x := exactSearchPoint f r direction x₀
      let s := fun j => x (j + 1) - x j
      let m := fun j => x j + (1 / 2 : ℝ) • s j
      ‖averagedDerivative H (x (k + 1)) (s (k + 1)) - averagedDerivative H (x k) (s k) -
        T (m (k + 1) - m k)‖ ≤ η * ‖x₀‖ := by
  intro η hη
  obtain ⟨δ, hδ, hrem⟩ := exactSearchPoint_midpoint_expansion f G H T hr hG₀ hH₀ hLr hH hF hG hD
    (η / 2) (by positivity)
  refine ⟨δ, hδ, ?_⟩
  intro x₀ hx₀ direction k
  dsimp only
  let x := exactSearchPoint f r direction x₀
  let s := fun j => x (j + 1) - x j
  let m := fun j => x j + (1 / 2 : ℝ) • s j
  let A := fun j => averagedDerivative H (x j) (s j)
  have h₀ : ‖A k - H 0 - T (m k)‖ ≤ (η / 2) * ‖x₀‖ := hrem x₀ hx₀ direction k
  have h₁ : ‖A (k + 1) - H 0 - T (m (k + 1))‖ ≤ (η / 2) * ‖x₀‖ :=
    hrem x₀ hx₀ direction (k + 1)
  have he : A (k + 1) - A k - T (m (k + 1) - m k) =
      (A (k + 1) - H 0 - T (m (k + 1))) - (A k - H 0 - T (m k)) := by
    rw [map_sub]
    abel
  change ‖A (k + 1) - A k - T (m (k + 1) - m k)‖ ≤ η * ‖x₀‖
  rw [he]
  exact (norm_sub_le _ _).trans ((add_le_add h₁ h₀).trans_eq (by ring))

end
end krylov.Functions
