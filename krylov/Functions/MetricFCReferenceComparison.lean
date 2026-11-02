import krylov.Functions.MetricFCSourceBounds
import krylov.Functions.FCReferenceFields

/-!
Article: main_krylov, lem:cycle-transfer, native FC quadratic-reference comparison.
Use: derive uniform second-order errors of actual physical line steps from
the real objective and its Hessian on the entire compact nondegenerate
quadratic reference family. Neither query bounds nor output remainders are assumed.
Source: Appendix G and the proved native execution/compact stability chain.
-/

namespace krylov.Functions
noncomputable section
open Set Metric krylov.Methods krylov.Reference krylov.Nonlinear
open scoped InnerProductSpace NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

/-- Actual physical full-memory FC line steps have uniform quadratic error relative to true CG steps.
Article: main_krylov, lem:cycle-transfer, the native FC reference-trajectory estimate.
Proof: derive actual gradient/operator input bounds from the original Hessian,
identify the entire actual execution with its true averaged-operator run,
apply compact analytic reference stability, then use genuine degree-one homogeneity. -/
theorem metricFCPoint_reference_steps (T : E ≃L[ℝ] E)
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
      ∀ u : E, ‖u‖ ≤ B → Q u ∈ K → ∀ i < N,
      ‖metricFCPoint T f G fullMemory r (ε • u) (i + 1) -
          metricFCPoint T f G fullMemory r (ε • u) i - ε • referenceStep Q (Q u) i‖ ≤ C * ε ^ 2 := by
  obtain ⟨δ, C, hδ, hC, hfields⟩ := compact_fc_reference_field_changes Q hQ hpos N K hK hpre
  let P : ℝ := (((‖T.toContinuousLinearMap‖₊ ^ 3 * L : ℝ≥0) : ℝ))
  let Dg : ℝ := P / 2 * B ^ 2
  let Da : ℝ := P * ‖T.symm.toContinuousLinearMap‖ * Real.sqrt 3 * ‖T.toContinuousLinearMap‖ * B
  let D : ℝ := Dg + Da + 1
  have hP : 0 ≤ P := NNReal.coe_nonneg _
  have hDg : 0 ≤ Dg := by dsimp only [Dg]; positivity
  have hDa : 0 ≤ Da := by dsimp only [Da]; positivity
  have hD : 0 < D := by dsimp only [D]; positivity
  let ε₀ := min (r / (4 * (‖T.toContinuousLinearMap‖ * B + 1))) (δ / (D + 1))
  have hε₀ : 0 < ε₀ := by dsimp only [ε₀]; positivity
  refine ⟨ε₀, C * D + 1, hε₀, by positivity, ?_⟩
  intro ε hε he u hu hKu i hi
  have huT : ‖T u‖ ≤ ‖T.toContinuousLinearMap‖ * B :=
    (T.toContinuousLinearMap.le_opNorm u).trans (mul_le_mul_of_nonneg_left hu (norm_nonneg _))
  have hx : ‖T (ε • u)‖ < r / 4 := by
    rw [map_smul, norm_smul, Real.norm_of_nonneg hε.le]
    have he' := (lt_div_iff₀ (by positivity : 0 < 4 * (‖T.toContinuousLinearMap‖ * B + 1))).mp
      (he.trans_le (min_le_left _ _))
    have hb := mul_le_mul_of_nonneg_left huT hε.le
    nlinarith
  have hx' : ‖T (ε • u)‖ ≤ r := by linarith [norm_nonneg (T (ε • u))]
  let A := metricFCOperator T f G H fullMemory r (ε • u)
  let g := Q u
  let v := ε⁻¹ • G (ε • u) - g
  let Θ : Fin N → E →L[ℝ] E := fun j => A j.val - Q
  have hv : ‖v‖ ≤ Dg * ε := by
    have ht := metric_gradient_quadratic_error T G H Q hr.le hG₀ hH₀ hH hG (ε • u) hx'
    have heq : v = ε⁻¹ • (G (ε • u) - Q (ε • u)) := by
      dsimp only [v, g]
      rw [smul_sub, map_smul, smul_smul, inv_mul_cancel₀ hε.ne', one_smul]
    rw [heq, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hε.le)]
    have hsq : ‖u‖ ^ 2 ≤ B ^ 2 := (sq_le_sq₀ (norm_nonneg _) hB.le).mpr hu
    rw [norm_smul, Real.norm_of_nonneg hε.le] at ht
    calc
      _ ≤ ε⁻¹ * (P / 2 * (ε * ‖u‖) ^ 2) := mul_le_mul_of_nonneg_left ht (inv_nonneg.mpr hε.le)
      _ = P / 2 * ‖u‖ ^ 2 * ε := by field_simp
      _ ≤ Dg * ε := by dsimp only [Dg]; nlinarith [mul_le_mul_of_nonneg_left hsq (by positivity : 0 ≤ P / 2 * ε)]
  have hA j : ‖A j - Q‖ ≤ Da * ε := by
    have ha := metricFCOperator_local_bound T hT f G H hr hG₀ hHc₀ hLr hH hF hG
      fullMemory (ε • u) (by linarith) j
    rw [hH₀, map_smul, norm_smul, Real.norm_of_nonneg hε.le] at ha
    change ‖A j - Q‖ ≤ _ at ha
    calc
      _ ≤ P * ‖T.symm.toContinuousLinearMap‖ * Real.sqrt 3 * (ε * ‖T u‖) := ha
      _ ≤ Da * ε := by
        have hb := mul_le_mul_of_nonneg_left huT
          (by positivity : 0 ≤ P * ‖T.symm.toContinuousLinearMap‖ * Real.sqrt 3 * ε)
        dsimp only [Da]
        nlinarith only [hb]
  have hΘ : ‖Θ‖ ≤ Da * ε := by
    apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ Da * ε)).mpr
    intro j
    exact hA j.val
  have hinput : ‖(v, Θ)‖ ≤ D * ε := by
    rw [Prod.norm_def, max_le_iff]
    constructor
    · exact hv.trans (by dsimp only [D]; nlinarith)
    · exact hΘ.trans (by dsimp only [D]; nlinarith)
  have hsmall : ‖(v, Θ)‖ ≤ δ := by
    have he' := (lt_div_iff₀ (by positivity : 0 < D + 1)).mp (he.trans_le (min_le_right _ _))
    exact hinput.trans (by nlinarith)
  have hs := (hfields g hKu v Θ hsmall i hi).2
  have hinit : G (ε • u) = ε • (g + v) := by
    dsimp only [v]
    rw [add_sub_cancel, smul_smul, mul_inv_cancel₀ hε.ne', one_smul]
  have hpath j (hj : j < N) : A j = fcFiniteOperatorPath Q N Θ j := by
    simp only [fcFiniteOperatorPath, dite_eq_left hj, Θ]
    abel
  have hscale := (fullFC_scalar (fcFiniteOperatorPath Q N Θ) (g + v) ε hε.ne' N).2 i hi
  rw [metricFCPoint_step_eq_fcStep T hT f G H hr hG₀ hHc₀ hLr hH hF hG
    fullMemory (ε • u) hx i, hinit,
    fcStep_congr_operator_prefix A (fcFiniteOperatorPath Q N Θ) (ε • (g + v)) N i hi hpath,
    hscale.2, ← smul_sub, norm_smul, Real.norm_of_nonneg hε.le]
  calc
    _ ≤ ε * (C * ‖(v, Θ)‖) := mul_le_mul_of_nonneg_left hs hε.le
    _ ≤ ε * (C * (D * ε)) := by gcongr
    _ ≤ (C * D + 1) * ε ^ 2 := by nlinarith [sq_nonneg ε]

end
end krylov.Functions
