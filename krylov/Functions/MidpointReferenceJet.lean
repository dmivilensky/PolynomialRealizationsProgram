import krylov.Functions.MidpointExpansion

/-!
Article: main_krylov, lem:cycle-transfer, genuine reference-midpoint replacement.
Use: turn derived real segment localization and derived quadratic reference
errors into the compatible first jet. This analytic lemma is reusable for
the actual own-A₀ FC and RFC wrappers.
Source: the true Hessian derivative and its proved uniform Bochner midpoint expansion.
-/

namespace krylov.Functions
noncomputable section
open Set Metric chebyshev1.Nonlinear
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Actual Hessian differentiability transfers every genuinely localized segment to its quadratically close reference midpoint, uniformly.
Article: main_krylov, lem:cycle-transfer, true compatible reference slice.
Proof: integrate the actual Frechet remainder uniformly over the original
segment, and bound the actual derivative on the real midpoint replacement error. -/
theorem averagedHessian_reference_jet (H : E → E →L[ℝ] F)
    (D : E →L[ℝ] E →L[ℝ] F) {r : ℝ} (hr : 0 < r)
    (hc : ContinuousOn H (ball 0 r)) (hD : HasFDerivAt H D 0)
    (M C : ℝ) (hM : 0 < M) (hC : 0 ≤ C) :
    ∀ η : ℝ, 0 < η → ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∀ a s m : E, (∀ t ∈ Icc (0 : ℝ) 1, ‖a + t • s‖ ≤ M * ε) →
      ‖a + (1 / 2 : ℝ) • s - ε • m‖ ≤ C * ε ^ 2 →
      ‖averagedDerivative H a s - H 0 - ε • D m‖ ≤ η * ε := by
  intro η hη
  obtain ⟨ρ, hρ, _, hrem⟩ := averagedHessian_midpoint_expansion H D hr hc hD (η / (2 * M)) (by positivity)
  let J := ‖D‖ * C
  have hJ : 0 ≤ J := by dsimp only [J]; positivity
  let ε₀ := min (ρ / M) (η / (2 * (J + 1)))
  refine ⟨ε₀, by dsimp only [ε₀]; positivity, ?_⟩
  intro ε hε he a s m hseg hmid
  have hρε : M * ε < ρ := by
    have he' := (lt_div_iff₀ hM).mp (he.trans_le (min_le_left _ _))
    nlinarith
  have hbase : ‖averagedDerivative H a s - H 0 - D (a + (1 / 2 : ℝ) • s)‖ ≤ η / 2 * ε := by
    exact (hrem (M * ε) (by positivity) hρε a s hseg).trans_eq (by field_simp)
  have hslice : ‖D (a + (1 / 2 : ℝ) • s) - ε • D m‖ ≤ η / 2 * ε := by
    rw [← map_smul, ← map_sub]
    have hb := (D.le_opNorm _).trans (mul_le_mul_of_nonneg_left hmid (norm_nonneg _))
    apply hb.trans
    rw [show ‖D‖ * (C * ε ^ 2) = J * ε ^ 2 by dsimp only [J]; ring]
    have he' := (lt_div_iff₀ (by positivity : 0 < 2 * (J + 1))).mp (he.trans_le (min_le_right _ _))
    nlinarith [mul_le_mul_of_nonneg_right he'.le hε.le]
  have heq : averagedDerivative H a s - H 0 - ε • D m =
      (averagedDerivative H a s - H 0 - D (a + (1 / 2 : ℝ) • s)) +
        (D (a + (1 / 2 : ℝ) • s) - ε • D m) := by abel
  rw [heq]
  exact (norm_add_le _ _).trans ((add_le_add hbase hslice).trans_eq (by ring))

end
end krylov.Functions
