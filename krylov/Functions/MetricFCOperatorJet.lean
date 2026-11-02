import krylov.Functions.MetricFCIncrementTransfer

/-!
Article: main_krylov, lem:cycle-transfer, actual physical FC secant first jets.
Use: identify every actual finite operator input with the same genuine third
derivative evaluated at the corresponding actual quadratic reference midpoint.
Source: the uniform Bochner midpoint expansion and the proved native physical
FC trajectory comparison. No localization or response remainder is assumed.
-/

namespace krylov.Functions
noncomputable section
open Set Metric krylov.Methods krylov.Reference krylov.Nonlinear chebyshev1.Nonlinear
open scoped InnerProductSpace NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

/-- The true physical quadratic reference segment midpoint.
Article: main_krylov, lem:cycle-transfer and thm:Htransfer. -/
def fcReferenceMidpoint (Q : E →L[ℝ] E) (u : E) (i : ℕ) : E :=
  fcQuadraticReferencePoint Q u i + (1 / 2 : ℝ) • referenceStep Q (Q u) i

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- The genuine physical Hessian is continuous on a concrete neighborhood of the minimizer.
Article: main_krylov, lem:cycle-transfer, physical midpoint domain. -/
theorem metric_hessian_continuous_ball (T : E ≃L[ℝ] E) (H : E → E →L[ℝ] E)
    {r : ℝ} {L : ℝ≥0}
    (hH : LipschitzOnWith L (coordinateDerivative T H) (closedBall 0 r)) :
    ContinuousOn H (ball 0 (r / (‖T.toContinuousLinearMap‖ + 1))) := by
  apply (coordinateDerivative_lipschitz_pullback T H hH).continuousOn.mono
  intro z hz
  change T z ∈ closedBall (0 : E) r
  rw [mem_closedBall, dist_zero_right]
  have hz' : ‖z‖ < r / (‖T.toContinuousLinearMap‖ + 1) := by
    simpa only [mem_ball, dist_zero_right] using hz
  have hb := (lt_div_iff₀ (by positivity : 0 < ‖T.toContinuousLinearMap‖ + 1)).mp hz'
  exact (T.toContinuousLinearMap.le_opNorm z).trans (by nlinarith [norm_nonneg z])

/-- Every actual physical FC secant has the compact-uniform genuine first jet at its true quadratic reference midpoint.
Article: main_krylov, lem:cycle-transfer and thm:Htransfer, full native FC input expansion.
Proof: actual native queries are localized from the objective. Integrate the
true Hessian derivative uniformly over their real segments, then replace the
actual midpoint by the genuine quadratic reference with its proved second-order error. -/
theorem metricFCOperator_reference_jet (T : E ≃L[ℝ] E)
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
      ∀ u : E, ‖u‖ ≤ B → Q u ∈ K → ∀ i : ℕ, i < N →
      ‖metricFCOperator T f G H fullMemory r (ε • u) i - Q -
        ε • D (fcReferenceMidpoint Q u i)‖ ≤ η * ε := by
  intro η hη
  let J := ‖T.toContinuousLinearMap‖
  let M := ‖T.symm.toContinuousLinearMap‖ * Real.sqrt 3 * J * B + 1
  have hJ : 0 ≤ J := norm_nonneg _
  have hM : 0 < M := by dsimp only [M]; positivity
  obtain ⟨ρ, hρ, _, hrem⟩ := averagedHessian_midpoint_expansion H D
    (by positivity : 0 < r / (‖T.toContinuousLinearMap‖ + 1))
    (metric_hessian_continuous_ball T H hH) hD (η / (2 * M)) (by positivity)
  obtain ⟨εp, C, hεp, hC, hpoints⟩ := metricFCPoint_reference_points T hT f G H Q hr hG₀ hH₀ hHc₀
    hLr hH hF hG hQ hpos N K hK hpre B hB
  let F := ‖D‖ * C
  have hF₀ : 0 ≤ F := by dsimp only [F]; positivity
  let ε₀ := min εp (min (r / (4 * (J * B + 1))) (min (ρ / M) (η / (2 * (F + 1)))))
  have hε₀ : 0 < ε₀ := by dsimp only [ε₀]; positivity
  refine ⟨ε₀, hε₀, ?_⟩
  intro ε hε he u hu hKu i hi
  let x := metricFCPoint T f G fullMemory r (ε • u)
  let a := x i
  let b := x (i + 1)
  let m := a + (1 / 2 : ℝ) • (b - a)
  let mq := fcReferenceMidpoint Q u i
  have huT : ‖T u‖ ≤ J * B :=
    (T.toContinuousLinearMap.le_opNorm u).trans (mul_le_mul_of_nonneg_left hu hJ)
  have hx₀ : ‖T (ε • u)‖ < r / 2 := by
    rw [map_smul, norm_smul, Real.norm_of_nonneg hε.le]
    have he' := (lt_div_iff₀ (by positivity : 0 < 4 * (J * B + 1))).mp
      (he.trans_le ((min_le_right _ _).trans (min_le_left _ _)))
    have hb := mul_le_mul_of_nonneg_left huT hε.le
    nlinarith
  have hloc := metricFCPoint_localization T hT f G H hr hG₀ hHc₀ hLr hH hF hG
    fullMemory (ε • u) hx₀
  have hb j : ‖x j‖ ≤ M * ε := by
    calc
      _ = ‖T.symm (T (x j))‖ := by rw [T.symm_apply_apply]
      _ ≤ ‖T.symm.toContinuousLinearMap‖ * ‖T (x j)‖ := T.symm.toContinuousLinearMap.le_opNorm _
      _ ≤ ‖T.symm.toContinuousLinearMap‖ * (Real.sqrt 3 * ‖T (ε • u)‖) := by
        exact mul_le_mul_of_nonneg_left (hloc j).1 (norm_nonneg _)
      _ ≤ M * ε := by
        rw [map_smul, norm_smul, Real.norm_of_nonneg hε.le]
        have hm := mul_le_mul_of_nonneg_left huT
          (by positivity : 0 ≤ ‖T.symm.toContinuousLinearMap‖ * Real.sqrt 3 * ε)
        dsimp only [M]
        nlinarith
  have hseg t (ht : t ∈ Icc (0 : ℝ) 1) : ‖a + t • (b - a)‖ ≤ M * ε := by
    have ha : a ∈ closedBall (0 : E) (M * ε) := by
      simpa only [mem_closedBall, dist_zero_right] using hb i
    have hb' : a + (b - a) ∈ closedBall (0 : E) (M * ε) := by
      simpa only [add_sub_cancel, mem_closedBall, dist_zero_right] using hb (i + 1)
    simpa only [mem_closedBall, dist_zero_right] using
      (convex_closedBall (0 : E) (M * ε)).add_smul_mem ha hb' ht
  have hρε : M * ε < ρ := by
    have he' := (lt_div_iff₀ hM).mp
      (he.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
    nlinarith
  have hbase : ‖averagedDerivative H a (b - a) - Q - D m‖ ≤ η / 2 * ε := by
    have hs := hrem (M * ε) (by positivity) hρε a (b - a) hseg
    rw [hH₀] at hs
    exact hs.trans_eq (by field_simp)
  have hmid : ‖m - ε • mq‖ ≤ C * ε ^ 2 := by
    have hp j (hj : j ≤ N) := hpoints ε hε (he.trans_le (min_le_left _ _)) u hu hKu j hj
    have hm := midpoint_error_bound a b (ε • fcQuadraticReferencePoint Q u i)
      (ε • fcQuadraticReferencePoint Q u (i + 1))
    have heq : m - ε • mq = (a + (1 / 2 : ℝ) • (b - a)) -
        (ε • fcQuadraticReferencePoint Q u i + (1 / 2 : ℝ) •
          (ε • fcQuadraticReferencePoint Q u (i + 1) - ε • fcQuadraticReferencePoint Q u i)) := by
      dsimp only [m, mq, fcReferenceMidpoint]
      rw [← fcQuadraticReferencePoint_step Q u i]
      module
    rw [heq]
    exact hm.trans (by nlinarith only [hp i (by omega), hp (i + 1) (by omega)])
  have hs : ‖D m - ε • D mq‖ ≤ η / 2 * ε := by
    rw [← map_smul, ← map_sub]
    have hbound := (D.le_opNorm _).trans (mul_le_mul_of_nonneg_left hmid (norm_nonneg _))
    have he' := (lt_div_iff₀ (by positivity : 0 < 2 * (F + 1))).mp
      (he.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
    apply hbound.trans
    rw [show ‖D‖ * (C * ε ^ 2) = F * ε ^ 2 by dsimp only [F]; ring]
    nlinarith [mul_le_mul_of_nonneg_right he'.le hε.le]
  change ‖averagedDerivative H a (b - a) - Q - ε • D mq‖ ≤ η * ε
  have heq : averagedDerivative H a (b - a) - Q - ε • D mq =
      (averagedDerivative H a (b - a) - Q - D m) + (D m - ε • D mq) := by abel
  rw [heq]
  exact (norm_add_le _ _).trans ((add_le_add hbase hs).trans_eq (by ring))

end
end krylov.Functions
