import krylov.Functions.MetricFCOwnIncrement

/-!
Article: main_krylov, lem:cycle-transfer, original-A₀ quadratic secant jets.
Use: derive the Lipschitz-third-derivative improvement with exactly the true
first-secant reference, retaining the actual initial gradient throughout.
Source: genuine quadratic midpoint Taylor and the proved own-reference query comparison.
-/

namespace krylov.Functions
noncomputable section
open Set Metric krylov.Methods krylov.Reference krylov.Nonlinear chebyshev1.Nonlinear
open scoped InnerProductSpace NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

/-- Actual FC secants have uniform quadratic third-derivative jets at their original own-A₀ reference midpoints.
Article: main_krylov, lem:cycle-transfer, the original-reference C³,¹ refinement.
Proof: the genuine native query bounds enclose each real segment in the
original metric domain. True quadratic midpoint Taylor and the derived
own-reference midpoint error give the common quadratic remainder. -/
theorem metricFCOperator_own_reference_quadratic_jet (T : E ≃L[ℝ] E)
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
    (N : ℕ) (K : Set ((E →L[ℝ] E) × E)) (hK : IsCompact K)
    (hquad : ∀ z ∈ K, z.1.toLinearMap.IsSymmetric ∧
      (∀ v : E, v ≠ 0 → 0 < inner ℝ v (z.1 v)) ∧ ∀ i < N, CG.gradient z.1 z.2 i ≠ 0)
    (B : ℝ) (hB : 0 < B) :
    ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∀ u : E, ‖u‖ ≤ B →
      let A := metricFCOperator T f G H fullMemory r (ε • u)
      let g := ε⁻¹ • G (ε • u)
      (A 0, g) ∈ K → ∀ i : ℕ, i < N →
      ‖A i - Q - ε • D 0 (fcOwnReferenceMidpoint (A 0) g u i)‖ ≤ C * ε ^ 2 := by
  obtain ⟨εp, C, hεp, hC, hpoints⟩ := metricFCPoint_own_reference_points T hT f G H Q hr hG₀ hH₀ hHc₀
    hLr hH hF hG N K hK hquad B hB
  obtain ⟨εq, M, hεq, hM, hquery⟩ := metricFCPoint_physical_bound T hT f G H hr hG₀ hHc₀ hLr hH hF hG B hB
  let S := T ⁻¹' closedBall (0 : E) r
  have hS : Convex ℝ S := by
    intro a ha b hb u v hu hv huv
    change T (u • a + v • b) ∈ closedBall (0 : E) r
    simpa only [map_add, map_smul] using (convex_closedBall (0 : E) r) ha hb hu hv huv
  have h₀ : (0 : E) ∈ S := by simp only [S, mem_preimage, map_zero, mem_closedBall, dist_self]; exact hr.le
  have hder z (hz : z ∈ S) : HasFDerivAt H (D z) z := by
    apply hD
    simpa only [S, mem_preimage, mem_closedBall, dist_zero_right] using hz
  refine ⟨min εp εq, (L₃ : ℝ) * M ^ 2 + ‖D 0‖ * C, lt_min hεp hεq, by positivity, ?_⟩
  intro ε hε he u hu
  dsimp only
  let A := metricFCOperator T f G H fullMemory r (ε • u)
  let g := ε⁻¹ • G (ε • u)
  intro hKref i hi
  let x := metricFCPoint T f G fullMemory r (ε • u)
  let a := x i
  let b := x (i + 1)
  let m := a + (1 / 2 : ℝ) • (b - a)
  let mq := fcOwnReferenceMidpoint (A 0) g u i
  let y := fun j => u + CG.displacement (A 0) g j
  have hq j := hquery ε hε (he.trans_le (min_le_right _ _)) u hu j
  have hp j (hj : j ≤ N) := hpoints ε hε (he.trans_le (min_le_left _ _)) u hu hKref j hj
  have hseg t (ht : t ∈ Icc (0 : ℝ) 1) : a + t • (b - a) ∈ S ∧ ‖a + t • (b - a)‖ ≤ M * ε := by
    constructor
    · apply hS.add_smul_mem
      · simpa only [S, mem_preimage, mem_closedBall, dist_zero_right] using (hq i).2.le
      · simpa only [add_sub_cancel, S, mem_preimage, mem_closedBall, dist_zero_right] using (hq (i + 1)).2.le
      · exact ht
    · have ha : a ∈ closedBall (0 : E) (M * ε) := by simpa only [mem_closedBall, dist_zero_right] using (hq i).1
      have hb : a + (b - a) ∈ closedBall (0 : E) (M * ε) := by
        simpa only [add_sub_cancel, mem_closedBall, dist_zero_right] using (hq (i + 1)).1
      simpa only [mem_closedBall, dist_zero_right] using (convex_closedBall (0 : E) (M * ε)).add_smul_mem ha hb ht
  have hbase := averagedHessian_midpoint_quadratic H D S hS h₀ hder hDlip a (b - a) (M * ε) (by positivity) hseg
  rw [hH₀] at hbase
  have hmid : ‖m - ε • mq‖ ≤ C * ε ^ 2 := by
    have hm := midpoint_error_bound a b (ε • y i) (ε • y (i + 1))
    have hy : y (i + 1) - y i = referenceStep (A 0) g i := by
      dsimp only [y]
      rw [CG.displacement_succ]
      unfold referenceStep
      module
    have heq : ε • mq = ε • y i + (1 / 2 : ℝ) • (ε • y (i + 1) - ε • y i) := by
      rw [← smul_sub, hy]
      dsimp only [mq, fcOwnReferenceMidpoint, y]
      module
    dsimp only [m]
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
