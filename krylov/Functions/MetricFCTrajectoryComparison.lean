import krylov.Functions.MetricFCReferenceComparison

/-!
Article: main_krylov, lem:cycle-transfer, actual physical FC query/reference comparison.
Use: telescope the already derived genuine physical step errors into uniform
second-order errors of all actual query points and segment midpoints.
Source: Appendix G, the true reference CG displacement and finite telescoping.
-/

namespace krylov.Functions
noncomputable section
open Set Metric krylov.Methods krylov.Reference krylov.Nonlinear
open scoped InnerProductSpace NNReal

/-- Actual step errors telescope to a quantitative error for every finite query prefix.
Article: main_krylov, lem:cycle-transfer, finite trajectory induction.
Proof: the new point error is the previous error plus the actual new step error. -/
theorem trajectory_step_error_bound {E : Type*} [NormedAddCommGroup E]
    (x y : ℕ → E) (N : ℕ) (C : ℝ) (h₀ : x 0 = y 0)
    (hstep : ∀ j < N, ‖(x (j + 1) - x j) - (y (j + 1) - y j)‖ ≤ C) :
    ∀ k ≤ N, ‖x k - y k‖ ≤ (k : ℝ) * C := by
  intro k hk
  induction k with
  | zero => simp only [h₀, sub_self, norm_zero, Nat.cast_zero, zero_mul, le_rfl]
  | succ k ih =>
    have hkN : k < N := by omega
    have he : x (k + 1) - y (k + 1) =
        (x k - y k) + ((x (k + 1) - x k) - (y (k + 1) - y k)) := by abel
    rw [he]
    calc
      _ ≤ ‖x k - y k‖ + ‖(x (k + 1) - x k) - (y (k + 1) - y k)‖ := norm_add_le _ _
      _ ≤ (k : ℝ) * C + C := add_le_add (ih (by omega)) (hstep k hkN)
      _ = _ := by push_cast; ring

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The genuine physical CG reference point starts at the original direction and sums the actual reference steps.
Article: main_krylov, lem:cycle-transfer, the reference queried trajectory. -/
def fcQuadraticReferencePoint (Q : E →L[ℝ] E) (u : E) (k : ℕ) : E :=
  u + CG.displacement Q (Q u) k

/-- The actual CG reference point advances by exactly its real reference step.
Article: main_krylov, lem:cycle-transfer. -/
theorem fcQuadraticReferencePoint_step (Q : E →L[ℝ] E) (u : E) (k : ℕ) :
    fcQuadraticReferencePoint Q u (k + 1) - fcQuadraticReferencePoint Q u k = referenceStep Q (Q u) k := by
  rw [fcQuadraticReferencePoint, fcQuadraticReferencePoint, CG.displacement_succ]
  unfold referenceStep
  abel

variable [CompleteSpace E] [FiniteDimensional ℝ E]

/-- Every actual physical FC query differs uniformly from its true quadratic reference by second order.
Article: main_krylov, lem:cycle-transfer, actual query and midpoint localization around the reference.
Proof: actual native step errors were derived from the function; telescope
them along the actual adaptive query sequence and true CG reference points. -/
theorem metricFCPoint_reference_points (T : E ≃L[ℝ] E)
    (hT : T.symm.toContinuousLinearMap.IsSymmetric)
    (f : E → ℝ) (G : E → E) (H : E → E →L[ℝ] E) (Q : E →L[ℝ] E)
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
    ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 < C ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∀ u : E, ‖u‖ ≤ B → Q u ∈ K → ∀ k ≤ N,
      ‖metricFCPoint T f G fullMemory r (ε • u) k - ε • fcQuadraticReferencePoint Q u k‖ ≤ C * ε ^ 2 := by
  obtain ⟨ε₀, C, hε₀, hC, hsteps⟩ := metricFCPoint_reference_steps T hT f G H Q hr hG₀ hH₀ hHc₀
    hLr hH hF hG hQ hpos N K hK hpre B hB
  refine ⟨ε₀, (N : ℝ) * C + 1, hε₀, by positivity, ?_⟩
  intro ε hε he u hu hKu k hk
  let x := metricFCPoint T f G fullMemory r (ε • u)
  let y := fun j => ε • fcQuadraticReferencePoint Q u j
  have hzero : x 0 = y 0 := by
    simp [x, y, metricFCPoint_zero, fcQuadraticReferencePoint, CG.displacement]
  have hys j : y (j + 1) - y j = ε • referenceStep Q (Q u) j := by
    dsimp only [y]
    rw [← smul_sub, fcQuadraticReferencePoint_step]
  have hs j (hj : j < N) : ‖(x (j + 1) - x j) - (y (j + 1) - y j)‖ ≤ C * ε ^ 2 := by
    rw [hys]
    exact hsteps ε hε he u hu hKu j hj
  have hb := trajectory_step_error_bound x y N (C * ε ^ 2) hzero hs k hk
  have hk' : (k : ℝ) ≤ N := by exact_mod_cast hk
  apply hb.trans
  calc
    _ ≤ (N : ℝ) * (C * ε ^ 2) :=
      mul_le_mul_of_nonneg_right hk' (mul_nonneg hC.le (sq_nonneg ε))
    _ ≤ _ := by nlinarith [sq_nonneg ε]

end
end krylov.Functions
