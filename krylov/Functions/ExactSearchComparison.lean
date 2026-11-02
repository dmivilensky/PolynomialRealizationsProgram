import krylov.Functions.LocalExactSearch

/-!
Article: main_krylov, lem:cycle-transfer, the genuine exact-search primitive.
Use: compare the actual local chord minimizer with the identity-Hessian
quadratic search, deriving its second-order displacement error from the
actual gradient and sharp endpoint enclosure. No query bound is assumed.
Source: Appendix G, stationarity and the genuine gradient Taylor remainder.
-/

namespace krylov.Functions
noncomputable section
open Set Metric
open scoped InnerProductSpace NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual line projection onto the minimizer of the identity quadratic.
Article: main_krylov, lem:cycle-transfer, the quadratic reference search. -/
def quadraticSearchPoint (x d : E) : E := x - (inner ℝ x d / ‖d‖ ^ 2) • d

/-- Stationarity alone compares an actual nonlinear search with the quadratic reference.
Article: main_krylov, lem:cycle-transfer.
Proof: the discrepancy is parallel to the search direction, whose scalar
component is exactly the actual gradient-model error in that direction. -/
theorem stationary_search_quadratic_comparison (G : E → E) (x d y : E)
    (hy : ∃ t : ℝ, y = x + t • d) (hstat : inner ℝ (G y) d = 0) :
    ‖y - quadraticSearchPoint x d‖ ≤ ‖G y - y‖ := by
  by_cases hd : d = 0
  · obtain ⟨t, ht⟩ := hy
    simp only [hd, smul_zero, add_zero] at ht
    simp [ht, hd, quadraticSearchPoint]
  obtain ⟨t, rfl⟩ := hy
  have hn : ‖d‖ ≠ 0 := norm_ne_zero_iff.mpr hd
  have he : x + t • d - quadraticSearchPoint x d =
      (t + inner ℝ x d / ‖d‖ ^ 2) • d := by
    dsimp only [quadraticSearchPoint]
    module
  have hpair : inner ℝ (G (x + t • d) - (x + t • d)) d =
      -(t + inner ℝ x d / ‖d‖ ^ 2) * ‖d‖ ^ 2 := by
    rw [inner_sub_left, hstat, inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
    field_simp
    ring
  have hb := abs_real_inner_le_norm (G (x + t • d) - (x + t • d)) d
  rw [hpair] at hb
  simp only [abs_mul, abs_neg, abs_sq] at hb
  rw [he, norm_smul, Real.norm_eq_abs]
  apply (mul_le_mul_iff_left₀ (norm_pos_iff.mpr hd)).mp
  convert! hb using 1
  ring

variable [CompleteSpace E]

/-- Actual exact searches differ from their quadratic search by a uniform second-order error.
Article: main_krylov, lem:cycle-transfer, genuine local exact-search comparison.
Proof: the constructed chord minimizer supplies stationarity and the sharp
square-root-three enclosure; the actual gradient Taylor error gives 3L/2. -/
theorem local_exact_search_quadratic_error (f : E → ℝ) (G : E → E)
    (H : E → E →L[ℝ] E) {r : ℝ} (hr : 0 < r)
    (hG₀ : G 0 = 0) (hH₀ : H 0 = ContinuousLinearMap.id ℝ E)
    {L : ℝ≥0} (hLr : (L : ℝ) * r ≤ 1 / 2)
    (hH : LipschitzOnWith L H (closedBall 0 r))
    (hF : ∀ z ∈ closedBall (0 : E) r, HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z ∈ closedBall (0 : E) r, HasFDerivAt G (H z) z)
    (x d y : E) (hx : ‖x‖ < r / 2) (hy : IsChordMinimum f x d r y) :
    ‖y - quadraticSearchPoint x d‖ ≤ 3 * (L : ℝ) / 2 * ‖x‖ ^ 2 := by
  have hs := local_chord_minimum_spec f G H hr hG₀ hH₀ hLr hH hF hG x d y hx hy
  have hrough : ‖y‖ ≤ Real.sqrt 3 * ‖x‖ := hs.1.trans
    (mul_le_mul_of_nonneg_right (min_le_left _ _) (norm_nonneg _))
  have hsq : ‖y‖ ^ 2 ≤ 3 * ‖x‖ ^ 2 := by
    have h := sq_le_sq₀ (norm_nonneg y) (mul_nonneg (Real.sqrt_nonneg 3) (norm_nonneg x))
    have hsqrt : (Real.sqrt (3 : ℝ)) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    have hb := h.mpr hrough
    rw [mul_pow, hsqrt] at hb
    exact hb
  have hTaylor := krylov.Nonlinear.gradient_model_quadratic_error G H
    (ContinuousLinearMap.id ℝ E) (closedBall 0 r) (convex_closedBall 0 r)
    (mem_closedBall_self hr.le) hH₀ hH hG y hy.1
  simp only [hG₀, sub_zero, ContinuousLinearMap.id_apply] at hTaylor
  calc
    _ ≤ ‖G y - y‖ := stationary_search_quadratic_comparison G x d y hy.2.1 hs.2.2.1
    _ ≤ (L : ℝ) / 2 * ‖y‖ ^ 2 := hTaylor
    _ ≤ 3 * (L : ℝ) / 2 * ‖x‖ ^ 2 := by nlinarith [L.coe_nonneg]

end
end krylov.Functions
