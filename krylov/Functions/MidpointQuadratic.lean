import krylov.Functions.MidpointExpansion
import Mathlib.Analysis.Calculus.MeanValue

/-!
Article: main_krylov, lem:cycle-transfer, Lipschitz-third-derivative refinement.
Use: derive a genuine quadratic midpoint remainder from the actual derivative
of the original Hessian and its genuine local Lipschitz bound.
Source: the derivative mean-value theorem on convex domains and the actual
Bochner segment integral. A coarse constant suffices for the stated order.
-/

namespace krylov.Functions
noncomputable section
open Set Metric MeasureTheory chebyshev1.Nonlinear
open scoped NNReal
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A genuine Lipschitz derivative gives a quadratic first-order remainder on every convex domain.
Article: main_krylov, lem:cycle-transfer, the genuine C³,¹ input estimate.
Proof: bound the derivative of the actual first-order remainder on the
intersection with the displacement ball, then apply the convex mean-value theorem. -/
theorem genuine_first_order_quadratic (H : E → F) (D : E → E →L[ℝ] F)
    (S : Set E) (hS : Convex ℝ S) (h₀ : (0 : E) ∈ S)
    (hD : ∀ z ∈ S, HasFDerivAt H (D z) z) {L : ℝ≥0} (hL : LipschitzOnWith L D S)
    (x : E) (hx : x ∈ S) : ‖H x - H 0 - D 0 x‖ ≤ (L : ℝ) * ‖x‖ ^ 2 := by
  let R := ‖x‖
  let U := S ∩ closedBall (0 : E) R
  let e := fun z => H z - H 0 - D 0 z
  have hder z (hz : z ∈ U) : HasFDerivAt e (D z - D 0) z :=
    ((hD z hz.1).sub_const (H 0)).sub (D 0).hasFDerivAt
  have hbound z (hz : z ∈ U) : ‖D z - D 0‖ ≤ (L : ℝ) * R := by
    have hb := hL.norm_sub_le hz.1 h₀
    rw [sub_zero] at hb
    exact hb.trans (mul_le_mul_of_nonneg_left (by simpa only [mem_closedBall, dist_zero_right] using hz.2) L.coe_nonneg)
  have hz : (0 : E) ∈ U := ⟨h₀, by simpa only [mem_closedBall, dist_self] using norm_nonneg x⟩
  have hx' : x ∈ U := ⟨hx, by simp only [mem_closedBall, dist_zero_right, R, le_rfl]⟩
  have hb := (hS.inter (convex_closedBall (0 : E) R)).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun z hz => (hder z hz).hasFDerivWithinAt) hbound hz hx'
  simpa only [e, sub_self, map_zero, sub_zero, R, pow_two, mul_assoc] using hb

variable [CompleteSpace F]

/-- A genuine Lipschitz third derivative gives a uniform quadratic actual-secant midpoint error.
Article: main_krylov, lem:cycle-transfer, the improved compatible-increment remainder.
Proof: integrate the proved true first-order Hessian remainder over the
actual segment and evaluate the affine part at its exact midpoint. -/
theorem averagedHessian_midpoint_quadratic (H : E → E →L[ℝ] F)
    (D : E → E →L[ℝ] E →L[ℝ] F) (S : Set E) (hS : Convex ℝ S) (h₀ : (0 : E) ∈ S)
    (hD : ∀ z ∈ S, HasFDerivAt H (D z) z) {L : ℝ≥0} (hL : LipschitzOnWith L D S)
    (a s : E) (R : ℝ) (hR : 0 ≤ R)
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1, a + t • s ∈ S ∧ ‖a + t • s‖ ≤ R) :
    ‖averagedDerivative H a s - H 0 - D 0 (a + (1 / 2 : ℝ) • s)‖ ≤ (L : ℝ) * R ^ 2 := by
  have hc : ContinuousOn (fun t : ℝ => H (a + t • s)) (Icc 0 1) := by
    apply ContinuousOn.comp (fun z hz => (hD z hz).continuousAt.continuousWithinAt)
      (continuous_const.add (continuous_id.smul continuous_const)).continuousOn
    exact fun t ht => (hseg t ht).1
  have hia := hc.intervalIntegrable_of_Icc (μ := volume) (by norm_num : (0 : ℝ) ≤ 1)
  have hib : IntervalIntegrable (fun t : ℝ => H 0 + D 0 (a + t • s)) volume 0 1 :=
    (by fun_prop : Continuous _).intervalIntegrable 0 1
  have heq : averagedDerivative H a s - H 0 - D 0 (a + (1 / 2 : ℝ) • s) =
      ∫ t in (0 : ℝ)..1, H (a + t • s) - (H 0 + D 0 (a + t • s)) := by
    rw [intervalIntegral.integral_sub hia hib]
    change averagedDerivative H a s - H 0 - D 0 (a + (1 / 2 : ℝ) • s) =
      averagedDerivative H a s - averagedDerivative (fun z => H 0 + D 0 z) a s
    rw [averagedHessian_affine]
    abel
  rw [heq]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
    (C := (L : ℝ) * R ^ 2) (f := fun t => H (a + t • s) - (H 0 + D 0 (a + t • s))) (fun t ht => ?_)
  · simpa only [sub_zero, abs_one, mul_one] using hb
  · rw [uIoc_of_le zero_le_one] at ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2⟩
    have hj := genuine_first_order_quadratic H D S hS h₀ hD hL (a + t • s) (hseg t ht').1
    have hsq : ‖a + t • s‖ ^ 2 ≤ R ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) hR).mpr (hseg t ht').2
    have hj' : ‖H (a + t • s) - (H 0 + D 0 (a + t • s))‖ ≤ (L : ℝ) * ‖a + t • s‖ ^ 2 := by
      simpa only [sub_add_eq_sub_sub] using hj
    exact hj'.trans
      (mul_le_mul_of_nonneg_left hsq L.coe_nonneg)

end
end krylov.Functions
