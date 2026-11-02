import krylov.Functions.MetricFCOperators

/-!
Article: main_krylov, lem:cycle-transfer, actual nonlinear FC source bounds.
Use: derive both actual segment-operator and initial-gradient perturbations
from the original physical Hessian, after native query localization has been
proved. These are genuine inputs to the compact operator stability theorem.
Source: Appendix G, the sharp endpoint integral and gradient Taylor theorem.
-/

namespace krylov.Functions
noncomputable section
open Set Metric krylov.Nonlinear chebyshev1.Nonlinear
open scoped InnerProductSpace NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Every actual physical FC segment operator has a derived linear perturbation bound at the cycle scale.
Article: main_krylov, lem:cycle-transfer, native actual operator input control.
Proof: localize the real queries in the actual metric, convert their norms to
physical norms, then apply the exact two-endpoint integral estimate to the
genuine physical Hessian and its original value at the minimizer. -/
theorem metricFCOperator_local_bound (T : E ≃L[ℝ] E)
    (hT : T.symm.toContinuousLinearMap.IsSymmetric)
    (f : E → ℝ) (G : E → E) (H : E → E →L[ℝ] E)
    {r : ℝ} (hr : 0 < r) (hG₀ : G 0 = 0)
    (hH₀ : coordinateDerivative T H 0 = ContinuousLinearMap.id ℝ E)
    {L : ℝ≥0} (hLr : (L : ℝ) * r ≤ 1 / 2)
    (hH : LipschitzOnWith L (coordinateDerivative T H) (closedBall 0 r))
    (hF : ∀ z : E, ‖T z‖ ≤ r → HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z : E, ‖T z‖ ≤ r → HasFDerivAt G (H z) z)
    (memory : ℕ → ℕ) (x₀ : E) (hx₀ : ‖T x₀‖ < r / 2) :
    ∀ k : ℕ, ‖metricFCOperator T f G H memory r x₀ k - H 0‖ ≤
      ((‖T.toContinuousLinearMap‖₊ ^ 3 * L : ℝ≥0) : ℝ) *
        ‖T.symm.toContinuousLinearMap‖ * Real.sqrt 3 * ‖T x₀‖ := by
  have hl := metricFCPoint_localization T hT f G H hr hG₀ hH₀ hLr hH hF hG memory x₀ hx₀
  have hphys := coordinateDerivative_lipschitz_pullback T H hH
  have hball j : metricFCPoint T f G memory r x₀ j ∈ T ⁻¹' closedBall (0 : E) r := by
    change T (metricFCPoint T f G memory r x₀ j) ∈ closedBall (0 : E) r
    simpa only [mem_closedBall, dist_zero_right] using (hl j).2.2.le
  have hb j : ‖metricFCPoint T f G memory r x₀ j‖ ≤
      ‖T.symm.toContinuousLinearMap‖ * (Real.sqrt 3 * ‖T x₀‖) := by
    calc
      _ = ‖T.symm (T (metricFCPoint T f G memory r x₀ j))‖ := by rw [T.symm_apply_apply]
      _ ≤ ‖T.symm.toContinuousLinearMap‖ * ‖T (metricFCPoint T f G memory r x₀ j)‖ :=
        T.symm.toContinuousLinearMap.le_opNorm _
      _ ≤ _ := mul_le_mul_of_nonneg_left (hl j).1 (norm_nonneg _)
  intro k
  let a := metricFCPoint T f G memory r x₀ k
  let b := metricFCPoint T f G memory r x₀ (k + 1)
  have hseg t (ht : t ∈ Icc (0 : ℝ) 1) : a + t • (b - a) ∈ T ⁻¹' closedBall (0 : E) r := by
    change T (a + t • (b - a)) ∈ closedBall (0 : E) r
    rw [map_add, map_smul, map_sub]
    apply (convex_closedBall (0 : E) r).add_smul_mem (hball k) _ ht
    change T a + (T b - T a) ∈ closedBall (0 : E) r
    simpa only [add_sub_cancel, mem_preimage, b] using hball (k + 1)
  have hc := hphys.continuousOn.comp
    (continuous_const.add (continuous_id.smul continuous_const)).continuousOn hseg
  have hz : (0 : E) ∈ T ⁻¹' closedBall (0 : E) r := by simp [hr.le]
  have hc₀ : ContinuousOn (fun t : ℝ => H ((0 : E) + t • (0 : E))) (Icc 0 1) := by
    simpa only [smul_zero, add_zero] using (continuousOn_const : ContinuousOn (fun _ : ℝ => H 0) (Icc 0 1))
  have hcomp := averagedHessian_endpoint_bound H a (b - a) 0 0
    (((‖T.toContinuousLinearMap‖₊ ^ 3 * L : ℝ≥0) : ℝ)) hc hc₀ (NNReal.coe_nonneg _)
    (fun t ht => by simpa only [smul_zero, add_zero] using hphys.norm_sub_le (hseg t ht) hz)
  have he : averagedDerivative H 0 0 = H 0 := by simp [averagedDerivative]
  rw [he] at hcomp
  simp only [sub_zero, add_sub_cancel, add_zero] at hcomp
  exact hcomp.trans (by
    have hsum := add_le_add (hb k) (hb (k + 1))
    change _ ≤ _
    nlinarith [mul_le_mul_of_nonneg_left hsum
      (NNReal.coe_nonneg (‖T.toContinuousLinearMap‖₊ ^ 3 * L))])

/-- The genuine physical gradient has its quadratic Taylor bound on the actual metric domain.
Article: main_krylov, lem:cycle-transfer, original initial-gradient source perturbation.
Proof: derive the original Hessian Lipschitz constant by metric pullback and
apply the existing actual gradient Taylor theorem on the convex metric ball. -/
theorem metric_gradient_quadratic_error (T : E ≃L[ℝ] E) (G : E → E)
    (H : E → E →L[ℝ] E) (Q : E →L[ℝ] E) {r : ℝ} (hr : 0 ≤ r)
    (hG₀ : G 0 = 0) (hH₀ : H 0 = Q) {L : ℝ≥0}
    (hH : LipschitzOnWith L (coordinateDerivative T H) (closedBall 0 r))
    (hG : ∀ z : E, ‖T z‖ ≤ r → HasFDerivAt G (H z) z)
    (x : E) (hx : ‖T x‖ ≤ r) :
    ‖G x - Q x‖ ≤ (((‖T.toContinuousLinearMap‖₊ ^ 3 * L : ℝ≥0) : ℝ)) / 2 * ‖x‖ ^ 2 := by
  let S := T ⁻¹' closedBall (0 : E) r
  have hS : Convex ℝ S := by
    intro a ha b hb u v hu hv huv
    change T (u • a + v • b) ∈ closedBall (0 : E) r
    simpa only [map_add, map_smul] using (convex_closedBall (0 : E) r) ha hb hu hv huv
  have hz : (0 : E) ∈ S := by simp [S, hr]
  have hder z (hz : z ∈ S) : HasFDerivAt G (H z) z := by
    apply hG
    simpa only [S, mem_preimage, mem_closedBall, dist_zero_right] using hz
  have hx' : x ∈ S := by simpa only [S, mem_preimage, mem_closedBall, dist_zero_right] using hx
  have hb := krylov.Nonlinear.gradient_model_quadratic_error G H Q S hS hz hH₀
    (coordinateDerivative_lipschitz_pullback T H hH) hder x hx'
  simpa only [hG₀, sub_zero] using hb

end
end krylov.Functions
