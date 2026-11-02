import krylov.Functions.FCOwnReferenceFields
import krylov.Functions.MetricFCLeadingSource

/-!
Article: main_krylov, lem:cycle-transfer and thm:Htransfer, original actual-A₀ reference comparison.
Use: retain the reference whose base is the true first segment secant and
whose initial gradient is the genuine observed gradient. Its complete step
and query comparison is derived uniformly over the original compact
nondegenerate reference family.
Source: genuine varying-reference compact FC fields, native embedding and
the actual source estimates. No reference-error bound is assumed.
-/

namespace krylov.Functions
noncomputable section
open Set Metric krylov.Methods krylov.Reference krylov.Nonlinear
open scoped InnerProductSpace NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

/-- Real native FC line steps differ quadratically from the original CG reference of their own first secant and observed initial gradient.
Article: main_krylov, lem:cycle-transfer and thm:Htransfer, original A₀ reference.
Proof: bound all genuine secants relative to the minimizer Hessian, then
relative to the actual first secant. The original compact nondegeneracy
assumption supplies a genuine common varying-reference tube. Exact native
embedding and true homogeneity identify the real physical step. -/
theorem metricFCPoint_own_reference_steps (T : E ≃L[ℝ] E)
    (hT : T.symm.toContinuousLinearMap.IsSymmetric)
    (f : E → ℝ) (G : E → E) (H : E → E →L[ℝ] E) (Q : E →L[ℝ] E)
    {r : ℝ} (hr : 0 < r) (hG₀ : G 0 = 0) (hH₀ : H 0 = Q)
    (hHc₀ : coordinateDerivative T H 0 = ContinuousLinearMap.id ℝ E)
    {L : ℝ≥0} (hLr : (L : ℝ) * r ≤ 1 / 2)
    (hH : LipschitzOnWith L (coordinateDerivative T H) (closedBall 0 r))
    (hF : ∀ z : E, ‖T z‖ ≤ r → HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z : E, ‖T z‖ ≤ r → HasFDerivAt G (H z) z)
    (N : ℕ) (K : Set ((E →L[ℝ] E) × E)) (hK : IsCompact K)
    (hquad : ∀ z ∈ K, z.1.toLinearMap.IsSymmetric ∧
      (∀ v : E, v ≠ 0 → 0 < inner ℝ v (z.1 v)) ∧ ∀ i < N, CG.gradient z.1 z.2 i ≠ 0)
    (B : ℝ) (hB : 0 < B) :
    ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 < C ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∀ u : E, ‖u‖ ≤ B →
      let A := metricFCOperator T f G H fullMemory r (ε • u)
      let g := ε⁻¹ • G (ε • u)
      (A 0, g) ∈ K → ∀ i < N,
      ‖metricFCPoint T f G fullMemory r (ε • u) (i + 1) -
          metricFCPoint T f G fullMemory r (ε • u) i - ε • referenceStep (A 0) g i‖ ≤ C * ε ^ 2 := by
  obtain ⟨δ, C, hδ, hC, hfields⟩ := compact_fc_own_reference_step_changes N K hK hquad
  obtain ⟨εs, P, hεs, hP, hsource⟩ := metricFCInput_bound T hT f G H Q hr hG₀ hH₀ hHc₀ hLr hH hF hG B hB
  let ε₀ := min εs (δ / (2 * P + 1))
  refine ⟨ε₀, 2 * C * P + 1, by dsimp only [ε₀]; positivity, by positivity, ?_⟩
  intro ε hε he u hu
  dsimp only
  let A := metricFCOperator T f G H fullMemory r (ε • u)
  let g := ε⁻¹ • G (ε • u)
  intro hKref i hi
  have hs := hsource ε hε (he.trans_le (min_le_left _ _)) u hu
  have ha j : ‖A j - Q‖ ≤ P * ε := by
    have hp := hs.2 (j + 1)
    exact (norm_le_pi_norm (metricFCInput T f G H Q r ε u (j + 1)).2 ⟨j, by omega⟩).trans
      ((norm_snd_le _).trans hp)
  let Θ : Fin N → E →L[ℝ] E := fun j => A j.val - A 0
  have hΘ : ‖Θ‖ ≤ 2 * P * ε := by
    apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ 2 * P * ε)).mpr
    intro j
    have heq : Θ j = (A j.val - Q) - (A 0 - Q) := by dsimp only [Θ]; abel
    rw [heq]
    exact (norm_sub_le _ _).trans (by nlinarith only [ha j.val, ha 0])
  have hsmall : ‖Θ‖ ≤ δ := by
    have he' := (lt_div_iff₀ (by positivity : 0 < 2 * P + 1)).mp (he.trans_le (min_le_right _ _))
    exact hΘ.trans (by nlinarith)
  have hfield := hfields (A 0, g) hKref Θ hsmall i hi
  have hpath j (hj : j < N) : A j = fcFiniteOperatorPath (A 0) N Θ j := by
    simp only [fcFiniteOperatorPath, dite_eq_left hj, Θ]
    abel
  have hinit : G (ε • u) = ε • g := by dsimp only [g]; rw [smul_smul, mul_inv_cancel₀ hε.ne', one_smul]
  have hscale := (fullFC_scalar (fcFiniteOperatorPath (A 0) N Θ) g ε hε.ne' N).2 i hi
  rw [metricFCPoint_step_eq_fcStep T hT f G H hr hG₀ hHc₀ hLr hH hF hG
    fullMemory (ε • u) hs.1 i, hinit,
    fcStep_congr_operator_prefix A (fcFiniteOperatorPath (A 0) N Θ) (ε • g) N i hi hpath,
    hscale.2, ← smul_sub, norm_smul, Real.norm_of_nonneg hε.le]
  simp only [smul_smul, inv_mul_cancel₀ hε.ne', one_smul]
  change ε * ‖fcStep fullMemory (fcFiniteOperatorPath (A 0) N Θ) g i - referenceStep (A 0) g i‖ ≤
    (2 * C * P + 1) * ε ^ 2
  calc
    _ ≤ ε * (C * ‖Θ‖) := mul_le_mul_of_nonneg_left hfield hε.le
    _ ≤ ε * (C * (2 * P * ε)) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hΘ hC.le) hε.le
    _ = (2 * C * P) * ε ^ 2 := by ring
    _ ≤ _ := by nlinarith [sq_nonneg ε]

/-- Every actual physical FC query has quadratic error relative to the original own-A₀ CG trajectory.
Article: main_krylov, lem:cycle-transfer, original reference query comparison.
Proof: telescope the true own-reference step comparison from the identical
actual initial point. Both the first segment secant and initial gradient are real observations. -/
theorem metricFCPoint_own_reference_points (T : E ≃L[ℝ] E)
    (hT : T.symm.toContinuousLinearMap.IsSymmetric)
    (f : E → ℝ) (G : E → E) (H : E → E →L[ℝ] E) (Q : E →L[ℝ] E)
    {r : ℝ} (hr : 0 < r) (hG₀ : G 0 = 0) (hH₀ : H 0 = Q)
    (hHc₀ : coordinateDerivative T H 0 = ContinuousLinearMap.id ℝ E)
    {L : ℝ≥0} (hLr : (L : ℝ) * r ≤ 1 / 2)
    (hH : LipschitzOnWith L (coordinateDerivative T H) (closedBall 0 r))
    (hF : ∀ z : E, ‖T z‖ ≤ r → HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z : E, ‖T z‖ ≤ r → HasFDerivAt G (H z) z)
    (N : ℕ) (K : Set ((E →L[ℝ] E) × E)) (hK : IsCompact K)
    (hquad : ∀ z ∈ K, z.1.toLinearMap.IsSymmetric ∧
      (∀ v : E, v ≠ 0 → 0 < inner ℝ v (z.1 v)) ∧ ∀ i < N, CG.gradient z.1 z.2 i ≠ 0)
    (B : ℝ) (hB : 0 < B) :
    ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 < C ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∀ u : E, ‖u‖ ≤ B →
      let A := metricFCOperator T f G H fullMemory r (ε • u)
      let g := ε⁻¹ • G (ε • u)
      (A 0, g) ∈ K → ∀ k ≤ N,
      ‖metricFCPoint T f G fullMemory r (ε • u) k -
        ε • (u + CG.displacement (A 0) g k)‖ ≤ C * ε ^ 2 := by
  obtain ⟨ε₀, C, hε₀, hC, hsteps⟩ := metricFCPoint_own_reference_steps T hT f G H Q hr hG₀ hH₀ hHc₀
    hLr hH hF hG N K hK hquad B hB
  refine ⟨ε₀, (N : ℝ) * C + 1, hε₀, by positivity, ?_⟩
  intro ε hε he u hu
  dsimp only
  let A := metricFCOperator T f G H fullMemory r (ε • u)
  let g := ε⁻¹ • G (ε • u)
  intro hKref k hk
  let x := metricFCPoint T f G fullMemory r (ε • u)
  let y := fun j => ε • (u + CG.displacement (A 0) g j)
  have hz : x 0 = y 0 := by simp [x, y, metricFCPoint_zero, CG.displacement]
  have hys j : y (j + 1) - y j = ε • referenceStep (A 0) g j := by
    dsimp only [y]
    rw [← smul_sub, CG.displacement_succ]
    unfold referenceStep
    module
  have hstep j (hj : j < N) : ‖(x (j + 1) - x j) - (y (j + 1) - y j)‖ ≤ C * ε ^ 2 := by
    rw [hys]
    exact hsteps ε hε he u hu hKref j hj
  have hb := trajectory_step_error_bound x y N (C * ε ^ 2) hz hstep k hk
  have hk' : (k : ℝ) ≤ N := by exact_mod_cast hk
  exact hb.trans ((mul_le_mul_of_nonneg_right hk' (by positivity : 0 ≤ C * ε ^ 2)).trans (by nlinarith [sq_nonneg ε]))

end
end krylov.Functions
