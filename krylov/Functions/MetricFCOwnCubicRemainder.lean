import krylov.Functions.MetricFCOwnLeading
import krylov.Functions.MetricFCOwnQuadraticJet

/-!
Article: main_krylov, lem:cycle-transfer, original-reference FC cubic remainder.
Use: close the true Lipschitz-third-derivative refinement with exactly the
actual first-secant base and actual observed initial gradient.
Source: genuine own-reference quadratic secant jets, actual compact varying-base
FC Taylor and exact native function/operator homogeneity.
-/

namespace krylov.Functions
noncomputable section
open Set Metric krylov.Methods krylov.Reference krylov.Nonlinear
open scoped InnerProductSpace NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

/-- Actual full FC has the original own-A₀ compatible response with a compact-uniform cubic remainder under a genuine Lipschitz third derivative.
Article: main_krylov, lem:cycle-transfer and thm:Htransfer, original-reference O(e³).
Proof: derive all actual own-base normalized input bounds and their genuine
quadratic compatible jets, then insert them in the actual uniform varying-base
FC Taylor theorem and use exact true FC homogeneity. -/
theorem metricFCPoint_own_cubic_remainder (T : E ≃L[ℝ] E)
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
    (K : Set ((E →L[ℝ] E) × E)) (hK : IsCompact K)
    (hquad : ∀ z ∈ K, z.1.toLinearMap.IsSymmetric ∧
      (∀ v : E, v ≠ 0 → 0 < inner ℝ v (z.1 v)) ∧
      ∀ i < Module.finrank ℝ E, CG.gradient z.1 z.2 i ≠ 0)
    (B : ℝ) (hB : 0 < B) :
    ∃ ε₀ R : ℝ, 0 < ε₀ ∧ 0 ≤ R ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∀ u : E, ‖u‖ ≤ B →
      let N := Module.finrank ℝ E
      let A := metricFCOperator T f G H fullMemory r (ε • u)
      let g := ε⁻¹ • G (ε • u)
      let m := fcOwnReferenceMidpoint (A 0) g u
      let W : Fin N → E →L[ℝ] E := fun i => D 0 (m i.val - m 0)
      (A 0, g) ∈ K →
      ‖G (metricFCPoint T f G fullMemory r (ε • u) N) -
        ε ^ 2 • fcLeadingOperator (A 0) N g W‖ ≤ R * ε ^ 3 := by
  let N := Module.finrank ℝ E
  obtain ⟨δ, C, M, hδ, hC, hM, hlead, htaylor⟩ := compact_fc_own_leading_operator K hK hquad
  obtain ⟨εs, P, hεs, hP, hsource⟩ := metricFCInput_bound T hT f G H Q hr hG₀ hH₀ hHc₀ hLr hH hF hG B hB
  obtain ⟨εj, J, hεj, hJ, hjet⟩ := metricFCOperator_own_reference_quadratic_jet T hT f G H Q D hr hG₀ hH₀ hHc₀
    hLr hH hF hG hD hDlip N K hK hquad B hB
  let ε₀ := min εs (min εj (δ / (2 * P + 1)))
  let R := 4 * C * P ^ 2 + 2 * M * J
  refine ⟨ε₀, R, by dsimp only [ε₀]; positivity, by dsimp only [R]; positivity, ?_⟩
  intro ε hε he u hu
  dsimp only
  let A := metricFCOperator T f G H fullMemory r (ε • u)
  let g := ε⁻¹ • G (ε • u)
  let m := fcOwnReferenceMidpoint (A 0) g u
  let W : Fin N → E →L[ℝ] E := fun i => D 0 (m i.val - m 0)
  let Θ : Fin N → E →L[ℝ] E := fun i => A i.val - A 0
  let F := fcOwnFiniteTerminal N ((A 0, g), Θ)
  let L₀ := fcLeadingOperator (A 0) N g W
  intro hKref
  have hs := hsource ε hε (he.trans_le (min_le_left _ _)) u hu
  have ha j : ‖A j - Q‖ ≤ P * ε :=
    (norm_le_pi_norm (metricFCInput T f G H Q r ε u (j + 1)).2 ⟨j, by omega⟩).trans
      ((norm_snd_le _).trans (hs.2 (j + 1)))
  have hΘ : ‖Θ‖ ≤ 2 * P * ε := by
    apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ 2 * P * ε)).mpr
    intro i
    have heq : Θ i = (A i.val - Q) - (A 0 - Q) := by dsimp only [Θ]; abel
    rw [heq]
    exact (norm_sub_le _ _).trans (by nlinarith only [ha i.val, ha 0])
  have hsmall : ‖Θ‖ ≤ δ := by
    have he' := (lt_div_iff₀ (by positivity : 0 < 2 * P + 1)).mp
      (he.trans_le ((min_le_right _ _).trans (min_le_right _ _)))
    exact hΘ.trans (by nlinarith)
  have hW : ‖Θ - ε • W‖ ≤ 2 * J * ε ^ 2 := by
    apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ 2 * J * ε ^ 2)).mpr
    intro i
    have hj := hjet ε hε (he.trans_le ((min_le_right _ _).trans (min_le_left _ _))) u hu hKref i.val i.isLt
    have hz := hjet ε hε (he.trans_le ((min_le_right _ _).trans (min_le_left _ _))) u hu hKref 0 (by have := i.isLt; omega)
    have heq : (Θ - ε • W) i = (A i.val - Q - ε • D 0 (m i.val)) - (A 0 - Q - ε • D 0 (m 0)) := by
      dsimp only [Θ, W, Pi.sub_apply, Pi.smul_apply]
      rw [map_sub, smul_sub]
      abel
    rw [heq]
    exact (norm_sub_le _ _).trans ((add_le_add hj hz).trans_eq (by ring))
  have hlin : fcLeadingOperator (A 0) N g (Θ - ε • W) =
      fcLeadingOperator (A 0) N g Θ - ε • L₀ := by
    change (fderiv ℝ (fcFiniteTerminal (A 0) N) (g, 0)) (0, Θ - ε • W) = _
    rw [show ((0 : E), Θ - ε • W) = (0, Θ) - ε • (0, W) by ext <;> simp, map_sub, map_smul]
    rfl
  have hresponse : ‖fcLeadingOperator (A 0) N g Θ - ε • L₀‖ ≤ 2 * M * J * ε ^ 2 := by
    have hb := hlead (A 0, g) hKref (Θ - ε • W)
    rw [hlin] at hb
    exact hb.trans ((mul_le_mul_of_nonneg_left hW hM).trans_eq (by ring))
  have hremainder : ‖F - fcLeadingOperator (A 0) N g Θ‖ ≤ 4 * C * P ^ 2 * ε ^ 2 := by
    have hb := htaylor (A 0, g) hKref Θ hsmall
    have hsq : ‖Θ‖ ^ 2 ≤ (2 * P * ε) ^ 2 := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hΘ
    exact hb.trans ((mul_le_mul_of_nonneg_left hsq hC).trans_eq (by ring))
  have htotal : ‖F - ε • L₀‖ ≤ R * ε ^ 2 := by
    have heq : F - ε • L₀ = (F - fcLeadingOperator (A 0) N g Θ) + (fcLeadingOperator (A 0) N g Θ - ε • L₀) := by abel
    rw [heq]
    exact (norm_add_le _ _).trans ((add_le_add hremainder hresponse).trans_eq (by dsimp only [R]; ring))
  have hactual : G (metricFCPoint T f G fullMemory r (ε • u) N) = ε • F := by
    have hb := metricFCPoint_gradient_eq_finiteTerminal T hT f G H (A 0) hr hG₀ hHc₀ hLr hH hF hG ε hε.ne' u hs.1 N
    simpa only [metricFCInput, add_sub_cancel, F, fcOwnFiniteTerminal, Θ, g, A] using hb
  rw [hactual]
  change ‖ε • F - ε ^ 2 • L₀‖ ≤ R * ε ^ 3
  rw [show ε • F - ε ^ 2 • L₀ = ε • (F - ε • L₀) by rw [smul_sub, smul_smul, pow_two],
    norm_smul, Real.norm_of_nonneg hε.le]
  exact (mul_le_mul_of_nonneg_left htotal hε.le).trans_eq (by ring)

end
end krylov.Functions
