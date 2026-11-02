import krylov.Functions.LocalPotential

/-!
Article: main_krylov, apG:E, quantitative enclosure of the exact line search.
Use: retain the printed square-root-three, first-order radius and step bounds
from the genuine cubic Taylor remainder, without postulating an iterate bound.
Source: the local quadratic comparison in Appendix G of main_krylov.
-/

namespace krylov.Functions
noncomputable section
open Set Metric
open scoped NNReal

/-- Comparing the two genuine cubic Taylor bounds encloses every sublevel point.
Article: main_krylov, apG:E. Proof: first obtain the coarse square comparison,
then feed the resulting bound back into the cubic terms. -/
theorem cubic_sublevel_radius {a b L r : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hL : 0 ≤ L) (har : a < r / 2) (hbr : b ≤ r) (hLr : L * r ≤ 1 / 2)
    (h : b ^ 2 / 2 - L * b ^ 3 / 6 ≤ a ^ 2 / 2 + L * a ^ 3 / 6) :
    b ≤ Real.sqrt 3 * a ∧ b ≤ (1 + 2 * L * a) * a ∧ b < r := by
  have hr : 0 < r := by linarith
  have har' : a ≤ r := by linarith
  have hLa : L * a ≤ 1 / 2 := (mul_le_mul_of_nonneg_left har' hL).trans hLr
  have hLb : L * b ≤ 1 / 2 := (mul_le_mul_of_nonneg_left hbr hL).trans hLr
  have hca : L * a ^ 3 ≤ a ^ 2 / 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hLa (sq_nonneg a)]
  have hcb : L * b ^ 3 ≤ b ^ 2 / 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hLb (sq_nonneg b)]
  have hsq : b ^ 2 ≤ 3 * a ^ 2 := by nlinarith
  have hs0 := Real.sqrt_nonneg (3 : ℝ)
  have hs2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have hs : (Real.sqrt 3 * a) ^ 2 = 3 * a ^ 2 := by rw [mul_pow, hs2]
  have hrough : b ≤ Real.sqrt 3 * a := by nlinarith [mul_nonneg hs0 ha]
  have htwo : b ≤ 2 * a := by nlinarith
  have hcube : b ^ 3 ≤ (2 * a) ^ 3 := by gcongr
  have hsharp : b ^ 2 ≤ a ^ 2 + 3 * L * a ^ 3 := by
    nlinarith [mul_le_mul_of_nonneg_left hcube hL]
  have hsharp' : b ≤ (1 + 2 * L * a) * a := by
    have hp : 0 ≤ L * a ^ 3 := by positivity
    apply (sq_le_sq₀ hb (by positivity : 0 ≤ (1 + 2 * L * a) * a)).mp
    nlinarith [sq_nonneg (2 * L * a ^ 2)]
  refine ⟨hrough, hsharp', ?_⟩
  have hslt : Real.sqrt 3 < 2 := by nlinarith
  have hprod := mul_le_mul_of_nonneg_right hslt.le ha
  -- The strict enclosure uses the square-root-three bound, not the coarse bound.
  exact (hrough.trans hprod).trans_lt (by linarith)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Every actual lower-valued chord point has all the printed local search bounds.
Article: main_krylov, apG:E.
Proof: apply the actual potential Taylor estimate at the two points, compare
their values, and use the scalar enclosure; the triangle inequality gives the
step bound. No property of a supplied trajectory is assumed. -/
theorem local_sublevel_search_bounds (f : E → ℝ) (G : E → E)
    (H : E → E →L[ℝ] E) {r : ℝ} (hr : 0 < r)
    (hG₀ : G 0 = 0) (hH₀ : H 0 = ContinuousLinearMap.id ℝ E)
    {L : ℝ≥0} (hLr : (L : ℝ) * r ≤ 1 / 2)
    (hH : LipschitzOnWith L H (closedBall 0 r))
    (hF : ∀ z ∈ closedBall (0 : E) r, HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z ∈ closedBall (0 : E) r, HasFDerivAt G (H z) z)
    (x y : E) (hx : ‖x‖ < r / 2) (hy : y ∈ closedBall (0 : E) r)
    (hvalue : f y ≤ f x) :
    ‖y‖ ≤ Real.sqrt 3 * ‖x‖ ∧ ‖y‖ ≤ (1 + 2 * (L : ℝ) * ‖x‖) * ‖x‖ ∧
      y ∈ ball (0 : E) r ∧ ‖y - x‖ ≤ 3 * ‖x‖ := by
  have hx' : x ∈ closedBall (0 : E) r := by
    rw [mem_closedBall, dist_zero_right]
    linarith [norm_nonneg x]
  have hzero : (0 : E) ∈ closedBall (0 : E) r := mem_closedBall_self hr.le
  have htx := potential_quadratic_error f G H (closedBall 0 r) (convex_closedBall 0 r)
    hzero hG₀ hH₀ hH hF hG x hx'
  have hty := potential_quadratic_error f G H (closedBall 0 r) (convex_closedBall 0 r)
    hzero hG₀ hH₀ hH hF hG y hy
  have hy' : ‖y‖ ≤ r := by simpa only [mem_closedBall, dist_zero_right] using hy
  have hv : ‖y‖ ^ 2 / 2 - (L : ℝ) * ‖y‖ ^ 3 / 6 ≤
      ‖x‖ ^ 2 / 2 + (L : ℝ) * ‖x‖ ^ 3 / 6 := by
    have htx' := abs_le.mp htx
    have hty' := abs_le.mp hty
    linarith
  obtain ⟨hrough, hsharp, hinter⟩ := cubic_sublevel_radius
    (norm_nonneg x) (norm_nonneg y) L.coe_nonneg hx hy' hLr hv
  refine ⟨hrough, hsharp, mem_ball_zero_iff.mpr hinter, ?_⟩
  have hs : Real.sqrt (3 : ℝ) ≤ 2 := by nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  calc
    ‖y - x‖ ≤ ‖y‖ + ‖x‖ := norm_sub_le _ _
    _ ≤ Real.sqrt 3 * ‖x‖ + ‖x‖ := add_le_add hrough le_rfl
    _ ≤ 3 * ‖x‖ := by nlinarith [mul_le_mul_of_nonneg_right hs (norm_nonneg x)]

end
end krylov.Functions
