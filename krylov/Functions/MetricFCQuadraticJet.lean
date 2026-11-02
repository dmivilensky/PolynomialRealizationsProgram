import krylov.Functions.MetricFCLeadingSource
import krylov.Functions.MidpointQuadratic

/-!
Article: main_krylov, lem:cycle-transfer, native Lipschitz-third-derivative input refinement.
Use: derive quadratic operator-input remainders for the actual physical FC
execution from a genuine Lipschitz third derivative of the original objective.
Source: actual native localization, real midpoint Taylor and true CG comparison.
-/

namespace krylov.Functions
noncomputable section
open Set Metric krylov.Methods krylov.Reference krylov.Nonlinear chebyshev1.Nonlinear
open scoped InnerProductSpace NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Every actual FC query has a uniform physical linear bound and lies in the true metric domain.
Article: main_krylov, lem:cycle-transfer, native query localization. -/
theorem metricFCPoint_physical_bound (T : E ≃L[ℝ] E)
    (hT : T.symm.toContinuousLinearMap.IsSymmetric)
    (f : E → ℝ) (G : E → E) (H : E → E →L[ℝ] E)
    {r : ℝ} (hr : 0 < r) (hG₀ : G 0 = 0)
    (hHc₀ : coordinateDerivative T H 0 = ContinuousLinearMap.id ℝ E)
    {L : ℝ≥0} (hLr : (L : ℝ) * r ≤ 1 / 2)
    (hH : LipschitzOnWith L (coordinateDerivative T H) (closedBall 0 r))
    (hF : ∀ z : E, ‖T z‖ ≤ r → HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z : E, ‖T z‖ ≤ r → HasFDerivAt G (H z) z)
    (B : ℝ) (hB : 0 < B) :
    ∃ ε₀ M : ℝ, 0 < ε₀ ∧ 0 < M ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∀ u : E, ‖u‖ ≤ B → ∀ j : ℕ,
      ‖metricFCPoint T f G fullMemory r (ε • u) j‖ ≤ M * ε ∧
      ‖T (metricFCPoint T f G fullMemory r (ε • u) j)‖ < r := by
  let J := ‖T.toContinuousLinearMap‖
  let M := ‖T.symm.toContinuousLinearMap‖ * Real.sqrt 3 * J * B + 1
  have hJ : 0 ≤ J := norm_nonneg _
  refine ⟨r / (4 * (J * B + 1)), M, by positivity, by dsimp only [M]; positivity, ?_⟩
  intro ε hε he u hu j
  have huT : ‖T u‖ ≤ J * B :=
    (T.toContinuousLinearMap.le_opNorm u).trans (mul_le_mul_of_nonneg_left hu hJ)
  have hx₀ : ‖T (ε • u)‖ < r / 2 := by
    rw [map_smul, norm_smul, Real.norm_of_nonneg hε.le]
    have he' := (lt_div_iff₀ (by positivity : 0 < 4 * (J * B + 1))).mp he
    have hb := mul_le_mul_of_nonneg_left huT hε.le
    nlinarith
  have hloc := metricFCPoint_localization T hT f G H hr hG₀ hHc₀ hLr hH hF hG
    fullMemory (ε • u) hx₀
  refine ⟨?_, (hloc j).2.2⟩
  calc
    _ = ‖T.symm (T (metricFCPoint T f G fullMemory r (ε • u) j))‖ := by rw [T.symm_apply_apply]
    _ ≤ ‖T.symm.toContinuousLinearMap‖ * ‖T (metricFCPoint T f G fullMemory r (ε • u) j)‖ :=
      T.symm.toContinuousLinearMap.le_opNorm _
    _ ≤ ‖T.symm.toContinuousLinearMap‖ * (Real.sqrt 3 * ‖T (ε • u)‖) :=
      mul_le_mul_of_nonneg_left (hloc j).1 (norm_nonneg _)
    _ ≤ M * ε := by
      rw [map_smul, norm_smul, Real.norm_of_nonneg hε.le]
      have hm := mul_le_mul_of_nonneg_left huT
        (by positivity : 0 ≤ ‖T.symm.toContinuousLinearMap‖ * Real.sqrt 3 * ε)
      dsimp only [M]
      nlinarith

variable [FiniteDimensional ℝ E]

/-- Genuine Lipschitz third derivatives give a compact-uniform quadratic error in every actual physical FC secant jet.
Article: main_krylov, lem:cycle-transfer, the actual improved FC input expansion.
Proof: true query localization encloses each real segment in both its original
metric domain and a shrinking physical ball. Apply the proved quadratic
midpoint remainder and the genuine quadratic reference-midpoint comparison. -/
theorem metricFCOperator_reference_quadratic_jet (T : E ≃L[ℝ] E)
    (hT : T.symm.toContinuousLinearMap.IsSymmetric)
    (f : E → ℝ) (G : E → E) (H : E → E →L[ℝ] E) (Q : E →L[ℝ] E)
    (D : E → E →L[ℝ] E →L[ℝ] E)
    {r : ℝ} (hr : 0 < r) (hG₀ : G 0 = 0) (hH₀ : H 0 = Q)
    (hHc₀ : coordinateDerivative T H 0 = ContinuousLinearMap.id ℝ E)
    {L L₃ : ℝ≥0} (hLr : (L : ℝ) * r ≤ 1 / 2)
    (hH : LipschitzOnWith L (coordinateDerivative T H) (closedBall 0 r))
    (hF : ∀ z : E, ‖T z‖ ≤ r → HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z : E, ‖T z‖ ≤ r → HasFDerivAt G (H z) z)
    (hD : ∀ z : E, ‖T z‖ ≤ r → HasFDerivAt H (D z) z)
    (hDlip : LipschitzOnWith L₃ D (T ⁻¹' closedBall (0 : E) r))
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E, v ≠ 0 → 0 < inner ℝ v (Q v))
    (N : ℕ) (K : Set E) (hK : IsCompact K)
    (hpre : ∀ g ∈ K, ∀ i < N, CG.gradient Q g i ≠ 0)
    (B : ℝ) (hB : 0 < B) :
    ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∀ u : E, ‖u‖ ≤ B → Q u ∈ K → ∀ i : ℕ, i < N →
      ‖metricFCOperator T f G H fullMemory r (ε • u) i - Q -
        ε • D 0 (fcReferenceMidpoint Q u i)‖ ≤ C * ε ^ 2 := by
  obtain ⟨εq, M, hεq, hM, hquery⟩ := metricFCPoint_physical_bound T hT f G H hr hG₀ hHc₀ hLr hH hF hG B hB
  obtain ⟨εp, C, hεp, hC, hpoints⟩ := metricFCPoint_reference_points T hT f G H Q hr hG₀ hH₀ hHc₀
    hLr hH hF hG hQ hpos N K hK hpre B hB
  let S := T ⁻¹' closedBall (0 : E) r
  have hS : Convex ℝ S := by
    intro a ha b hb u v hu hv huv
    change T (u • a + v • b) ∈ closedBall (0 : E) r
    simpa only [map_add, map_smul] using (convex_closedBall (0 : E) r) ha hb hu hv huv
  have h₀ : (0 : E) ∈ S := by simp only [S, mem_preimage, map_zero, mem_closedBall, dist_self]; exact hr.le
  have hder z (hz : z ∈ S) : HasFDerivAt H (D z) z := by
    apply hD
    simpa only [S, mem_preimage, mem_closedBall, dist_zero_right] using hz
  refine ⟨min εq εp, (L₃ : ℝ) * M ^ 2 + ‖D 0‖ * C, lt_min hεq hεp, by positivity, ?_⟩
  intro ε hε he u hu hKu i hi
  let x := metricFCPoint T f G fullMemory r (ε • u)
  let a := x i
  let b := x (i + 1)
  let m := a + (1 / 2 : ℝ) • (b - a)
  let mq := fcReferenceMidpoint Q u i
  have hq j := hquery ε hε (he.trans_le (min_le_left _ _)) u hu j
  have hseg t (ht : t ∈ Icc (0 : ℝ) 1) : a + t • (b - a) ∈ S ∧ ‖a + t • (b - a)‖ ≤ M * ε := by
    constructor
    · apply hS.add_smul_mem
      · simpa only [S, mem_preimage, mem_closedBall, dist_zero_right] using (hq i).2.le
      · simpa only [add_sub_cancel, S, mem_preimage, mem_closedBall, dist_zero_right] using (hq (i + 1)).2.le
      · exact ht
    · have ha : a ∈ closedBall (0 : E) (M * ε) := by
        simpa only [mem_closedBall, dist_zero_right] using (hq i).1
      have hb : a + (b - a) ∈ closedBall (0 : E) (M * ε) := by
        simpa only [add_sub_cancel, mem_closedBall, dist_zero_right] using (hq (i + 1)).1
      simpa only [mem_closedBall, dist_zero_right] using (convex_closedBall (0 : E) (M * ε)).add_smul_mem ha hb ht
  have hbase := averagedHessian_midpoint_quadratic H D S hS h₀ hder hDlip a (b - a) (M * ε) (by positivity) hseg
  rw [hH₀] at hbase
  have hmid : ‖m - ε • mq‖ ≤ C * ε ^ 2 := by
    have hp j (hj : j ≤ N) := hpoints ε hε (he.trans_le (min_le_right _ _)) u hu hKu j hj
    have hm := midpoint_error_bound a b (ε • fcQuadraticReferencePoint Q u i) (ε • fcQuadraticReferencePoint Q u (i + 1))
    have heq : m - ε • mq = (a + (1 / 2 : ℝ) • (b - a)) -
        (ε • fcQuadraticReferencePoint Q u i + (1 / 2 : ℝ) •
          (ε • fcQuadraticReferencePoint Q u (i + 1) - ε • fcQuadraticReferencePoint Q u i)) := by
      dsimp only [m, mq, fcReferenceMidpoint]
      rw [← fcQuadraticReferencePoint_step Q u i]
      module
    rw [heq]
    exact hm.trans (by nlinarith only [hp i (by omega), hp (i + 1) (by omega)])
  have hslice : ‖D 0 m - ε • D 0 mq‖ ≤ ‖D 0‖ * (C * ε ^ 2) := by
    rw [← map_smul, ← map_sub]
    exact ((D 0).le_opNorm _).trans (mul_le_mul_of_nonneg_left hmid (norm_nonneg _))
  change ‖averagedDerivative H a (b - a) - Q - ε • D 0 mq‖ ≤ _
  have heq : averagedDerivative H a (b - a) - Q - ε • D 0 mq =
      (averagedDerivative H a (b - a) - Q - D 0 m) + (D 0 m - ε • D 0 mq) := by abel
  rw [heq]
  exact (norm_add_le _ _).trans ((add_le_add hbase hslice).trans_eq (by ring))

end
end krylov.Functions
