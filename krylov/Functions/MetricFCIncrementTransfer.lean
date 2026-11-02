import krylov.Functions.MetricFCTrajectoryComparison
import krylov.Functions.SearchMidpointTransfer

/-!
Article: main_krylov, thm:Htransfer, uniform compatible native FC increments.
Use: replace actual queried midpoints by the genuine compact-family quadratic
reference, using derived native second-order trajectory control. The genuine
third derivative is transported through the actual reference metric.
Source: Appendix G, actual midpoint FTC and the proved native query comparison.
-/

namespace krylov.Functions
noncomputable section
open Set Metric krylov.Methods krylov.Reference krylov.Nonlinear chebyshev1.Nonlinear
open scoped InnerProductSpace NNReal

/-- Midpoint errors are bounded by the arithmetic mean of the true endpoint errors.
Article: main_krylov, lem:cycle-transfer, actual midpoint replacement. -/
theorem midpoint_error_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a b c d : E) :
    ‖(a + (1 / 2 : ℝ) • (b - a)) - (c + (1 / 2 : ℝ) • (d - c))‖ ≤
      (‖a - c‖ + ‖b - d‖) / 2 := by
  have he : (a + (1 / 2 : ℝ) • (b - a)) - (c + (1 / 2 : ℝ) • (d - c)) =
      (1 / 2 : ℝ) • ((a - c) + (b - d)) := by module
  rw [he, norm_smul]
  norm_num
  exact (mul_le_mul_of_nonneg_left (norm_add_le _ _) (by norm_num : (0 : ℝ) ≤ 1 / 2)).trans_eq (by ring)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

/-- The true physical quadratic reference midpoint in the actual canonical coordinates.
Article: main_krylov, thm:Htransfer, the reference midpoint displacement. -/
def fcReferenceMetricMidpoint (T : E ≃L[ℝ] E) (Q : E →L[ℝ] E) (u : E) (i : ℕ) : E :=
  T (fcQuadraticReferencePoint Q u i + (1 / 2 : ℝ) • referenceStep Q (Q u) i)

/-- Actual native FC Hessian increments are compatible slices of the genuine third derivative at the true reference midpoints.
Article: main_krylov, thm:Htransfer, uniform FC increment transfer.
Proof: obtain all real native query and reference errors from the original
objective. Apply the genuine uniform midpoint expansion, replace the actual
midpoint differences by their true quadratic references with the proved
second-order error, and absorb that error uniformly in the cycle scale. -/
theorem metricFCPoint_reference_increment (T : E ≃L[ℝ] E)
    (hT : T.symm.toContinuousLinearMap.IsSymmetric)
    (f : E → ℝ) (G : E → E) (H : E → E →L[ℝ] E) (Q : E →L[ℝ] E)
    (D : E →L[ℝ] E →L[ℝ] E) (hD : HasFDerivAt H D 0)
    {r : ℝ} (hr : 0 < r) (hG₀ : G 0 = 0) (hH₀ : H 0 = Q)
    (hHc₀ : coordinateDerivative T H 0 = ContinuousLinearMap.id ℝ E)
    {L : ℝ≥0} (hLr : (L : ℝ) * r ≤ 1 / 2)
    (hH : LipschitzOnWith L (coordinateDerivative T H) (closedBall 0 r))
    (hF : ∀ z : E, ‖T z‖ ≤ r → HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z : E, ‖T z‖ ≤ r → HasFDerivAt G (H z) z)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E, v ≠ 0 → 0 < inner ℝ v (Q v))
    (N : ℕ) (K : Set E) (hK : IsCompact K)
    (hpre : ∀ g ∈ K, ∀ i < N, CG.gradient Q g i ≠ 0)
    (B : ℝ) (hB : 0 < B) :
    ∀ η : ℝ, 0 < η → ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∀ u : E, ‖u‖ ≤ B → Q u ∈ K → ∀ i : ℕ, i + 1 < N →
      let x := metricFCPoint T f G fullMemory r (ε • u)
      let A := fun j => averagedDerivative (coordinateDerivative T H) (T (x j)) (T (x (j + 1) - x j))
      ‖A (i + 1) - A i - ε • coordinateHessianVariation T (fun _ => D) 0
        (fcReferenceMetricMidpoint T Q u (i + 1) - fcReferenceMetricMidpoint T Q u i)‖ ≤ η * ε := by
  intro η hη
  let Dc := coordinateHessianVariation T (fun _ => D) 0
  have hDc : HasFDerivAt (coordinateDerivative T H) Dc 0 := by
    apply coordinateDerivative_hasFDerivAt T H (fun _ => D) 0
    simpa only [map_zero] using hD
  have hFc z (hz : z ∈ closedBall (0 : E) r) :
      HasFDerivAt (coordinateObjective T f) (innerSL ℝ (coordinateGradient T G z)) z := by
    apply coordinateObjective_hasFDerivAt T hT f G z
    apply hF
    simpa only [T.apply_symm_apply, mem_closedBall, dist_zero_right] using hz
  have hGc z (hz : z ∈ closedBall (0 : E) r) :
      HasFDerivAt (coordinateGradient T G) (coordinateDerivative T H z) z := by
    apply coordinateGradient_hasFDerivAt T G H z
    apply hG
    simpa only [T.apply_symm_apply, mem_closedBall, dist_zero_right] using hz
  have hg₀ : coordinateGradient T G 0 = 0 := by simp only [coordinateGradient, map_zero, hG₀]
  let J := ‖T.toContinuousLinearMap‖
  have hJ : 0 ≤ J := norm_nonneg _
  obtain ⟨δ, hδ, hinc⟩ := exactSearchPoint_hessian_increment (coordinateObjective T f)
    (coordinateGradient T G) (coordinateDerivative T H) Dc hr hg₀ hHc₀ hLr hH hFc hGc hDc
    (η / (2 * (J * B + 1))) (by positivity)
  obtain ⟨εp, C, hεp, hC, hpoints⟩ := metricFCPoint_reference_points T hT f G H Q hr hG₀ hH₀ hHc₀
    hLr hH hF hG hQ hpos N K hK hpre B hB
  let F := 2 * ‖Dc‖ * J * C
  have hFn : 0 ≤ F := by dsimp only [F]; positivity
  let ε₀ := min εp (min (δ / (J * B + 1)) (η / (2 * (F + 1))))
  have hε₀ : 0 < ε₀ := by dsimp only [ε₀]; positivity
  refine ⟨ε₀, hε₀, ?_⟩
  intro ε hε he u hu hKu i hi
  let x := metricFCPoint T f G fullMemory r (ε • u)
  let m := fun j => T (x j) + (1 / 2 : ℝ) • T (x (j + 1) - x j)
  let q := fun j => T (fcQuadraticReferencePoint Q u j)
  let mq := fcReferenceMetricMidpoint T Q u
  let A := fun j => averagedDerivative (coordinateDerivative T H) (T (x j)) (T (x (j + 1) - x j))
  have hεp' : ε < εp := he.trans_le (min_le_left _ _)
  have hmid j (hj : j + 1 ≤ N) : ‖m j - ε • mq j‖ ≤ J * C * ε ^ 2 := by
    have hp k (hk : k ≤ N) : ‖T (x k) - ε • q k‖ ≤ J * (C * ε ^ 2) := by
      have hn := T.toContinuousLinearMap.le_opNorm (x k - ε • fcQuadraticReferencePoint Q u k)
      rw [map_sub, map_smul] at hn
      exact hn.trans (mul_le_mul_of_nonneg_left (hpoints ε hε hεp' u hu hKu k hk) hJ)
    have hb := midpoint_error_bound (T (x j)) (T (x (j + 1))) (ε • q j) (ε • q (j + 1))
    have heq : m j - ε • mq j = (T (x j) + (1 / 2 : ℝ) • (T (x (j + 1)) - T (x j))) -
        (ε • q j + (1 / 2 : ℝ) • (ε • q (j + 1) - ε • q j)) := by
      dsimp only [m, mq, q, fcReferenceMetricMidpoint]
      rw [← fcQuadraticReferencePoint_step Q u j]
      simp only [map_add, map_smul, map_sub]
      module
    rw [heq]
    exact hb.trans (by nlinarith only [hp j (by omega), hp (j + 1) hj])
  have hdiff : ‖(m (i + 1) - m i) - ε • (mq (i + 1) - mq i)‖ ≤ 2 * J * C * ε ^ 2 := by
    have heq : (m (i + 1) - m i) - ε • (mq (i + 1) - mq i) =
        (m (i + 1) - ε • mq (i + 1)) - (m i - ε • mq i) := by module
    rw [heq]
    exact (norm_sub_le _ _).trans (by nlinarith only [hmid (i + 1) (by omega), hmid i (by omega)])
  have hslice : ‖Dc (m (i + 1) - m i) - ε • Dc (mq (i + 1) - mq i)‖ ≤ F * ε ^ 2 := by
    rw [← map_smul, ← map_sub]
    exact (Dc.le_opNorm _).trans ((mul_le_mul_of_nonneg_left hdiff (norm_nonneg _)).trans_eq (by dsimp only [F]; ring))
  have hTu : ‖T u‖ ≤ J * B :=
    (T.toContinuousLinearMap.le_opNorm u).trans (mul_le_mul_of_nonneg_left hu hJ)
  have hxδ : ‖T (ε • u)‖ < δ := by
    rw [map_smul, norm_smul, Real.norm_of_nonneg hε.le]
    have he' := (lt_div_iff₀ (by positivity : 0 < J * B + 1)).mp
      (he.trans_le ((min_le_right _ _).trans (min_le_left _ _)))
    have hb := mul_le_mul_of_nonneg_left hTu hε.le
    nlinarith
  have ha := hinc (T (ε • u)) hxδ (metricFCDirection T G fullMemory (ε • u)) i
  have ha' : ‖A (i + 1) - A i - Dc (m (i + 1) - m i)‖ ≤
      η / (2 * (J * B + 1)) * ‖T (ε • u)‖ := by
    simpa only [A, m, x, metricFCPoint, map_sub, T.apply_symm_apply] using ha
  have hbase : ‖A (i + 1) - A i - Dc (m (i + 1) - m i)‖ ≤ η / 2 * ε := by
    have hb : ‖T (ε • u)‖ ≤ ε * (J * B) := by
      rw [map_smul, norm_smul, Real.norm_of_nonneg hε.le]
      exact mul_le_mul_of_nonneg_left hTu hε.le
    apply ha'.trans
    calc
      _ ≤ η / (2 * (J * B + 1)) * (ε * (J * B + 1)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact hb.trans (by nlinarith)
      _ = _ := by field_simp
  have hsmall : F * ε ^ 2 ≤ η / 2 * ε := by
    have he' := (lt_div_iff₀ (by positivity : 0 < 2 * (F + 1))).mp
      (he.trans_le ((min_le_right _ _).trans (min_le_right _ _)))
    nlinarith [mul_le_mul_of_nonneg_right he'.le hε.le]
  change ‖A (i + 1) - A i - ε • Dc (mq (i + 1) - mq i)‖ ≤ η * ε
  have heq : A (i + 1) - A i - ε • Dc (mq (i + 1) - mq i) =
      (A (i + 1) - A i - Dc (m (i + 1) - m i)) +
        (Dc (m (i + 1) - m i) - ε • Dc (mq (i + 1) - mq i)) := by abel
  rw [heq]
  exact (norm_add_le _ _).trans ((add_le_add hbase (hslice.trans hsmall)).trans_eq (by ring))

end
end krylov.Functions
