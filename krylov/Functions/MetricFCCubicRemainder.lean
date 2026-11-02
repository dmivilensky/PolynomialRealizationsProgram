import krylov.Functions.MetricFCQuadraticJet
import krylov.Functions.MetricFCSpatialResponse

/-!
Article: main_krylov, lem:cycle-transfer, full native FC cubic remainder.
Use: upgrade the actual degree-two compatible-tensor FC expansion to a true
compact-uniform cubic error from the genuine Lipschitz third derivative.
Source: real quadratic midpoint errors and the actual compact FC Taylor tube.
-/

namespace krylov.Functions
noncomputable section
open Set Metric krylov.Methods krylov.Reference krylov.Nonlinear
open scoped InnerProductSpace NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

/-- Actual native full FC has a compact-uniform cubic remainder when the genuine third derivative is Lipschitz.
Article: main_krylov, lem:cycle-transfer and thm:Htransfer, the FC O(e³) refinement.
Proof: every true operator input has its derived quadratic compatible jet.
The genuine finite FC Taylor remainder is quadratic in the actual normalized
inputs; its first derivative kills all initial-gradient drift. Actual FC
homogeneity supplies the remaining factor of the cycle scale. -/
theorem metricFCPoint_cubic_remainder (T : E ≃L[ℝ] E)
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
    (K : Set E) (hK : IsCompact K)
    (hpre : ∀ g ∈ K, ∀ i < Module.finrank ℝ E, CG.gradient Q g i ≠ 0)
    (B : ℝ) (hB : 0 < B) :
    ∃ ε₀ R : ℝ, 0 < ε₀ ∧ 0 ≤ R ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∀ u : E, ‖u‖ ≤ B → Q u ∈ K →
      ‖G (metricFCPoint T f G fullMemory r (ε • u) (Module.finrank ℝ E)) -
        ε ^ 2 • fcTensorLeading Q (D 0) u‖ ≤ R * ε ^ 3 := by
  let N := Module.finrank ℝ E
  obtain ⟨δ, C, M, hδ, hC, hM, hlead, htaylor⟩ := compact_fc_leading_operator Q hQ hpos K hK hpre
  obtain ⟨εs, P, hεs, hP, hsource⟩ := metricFCInput_bound T hT f G H Q hr hG₀ hH₀ hHc₀ hLr hH hF hG B hB
  obtain ⟨εj, J, hεj, hJ, hjet⟩ := metricFCOperator_reference_quadratic_jet T hT f G H Q D hr hG₀ hH₀ hHc₀
    hLr hH hF hG hD hDlip hQ hpos N K hK hpre B hB
  let ε₀ := min εs (min εj (δ / (P + 1)))
  let R := C * P ^ 2 + M * J
  refine ⟨ε₀, R, by dsimp only [ε₀]; positivity, by dsimp only [R]; positivity, ?_⟩
  intro ε hε he u hu hKu
  let I := metricFCInput T f G H Q r ε u N
  let S : Fin N → E →L[ℝ] E := fun i => D 0 (fcReferenceMidpoint Q u i.val)
  let F := fcFiniteTerminal Q N (Q u + I.1, I.2)
  let L₀ := fcLeadingOperator Q N (Q u) S
  have hs := hsource ε hε (he.trans_le (min_le_left _ _)) u hu
  have hi : ‖I‖ ≤ P * ε := hs.2 N
  have hismall : ‖I‖ ≤ δ := by
    have he' := (lt_div_iff₀ (by positivity : 0 < P + 1)).mp
      (he.trans_le ((min_le_right _ _).trans (min_le_right _ _)))
    exact hi.trans (by nlinarith)
  have hΘ : ‖I.2 - ε • S‖ ≤ J * ε ^ 2 := by
    apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ J * ε ^ 2)).mpr
    intro i
    exact hjet ε hε (he.trans_le ((min_le_right _ _).trans (min_le_left _ _))) u hu hKu i.val i.isLt
  have hlin : fcLeadingOperator Q N (Q u) (I.2 - ε • S) =
      fcLeadingOperator Q N (Q u) I.2 - ε • L₀ := by
    change (fderiv ℝ (fcFiniteTerminal Q N) (Q u, 0)) (0, I.2 - ε • S) = _
    rw [show ((0 : E), I.2 - ε • S) = (0, I.2) - ε • (0, S) by ext <;> simp,
      map_sub, map_smul]
    rfl
  have hresponse : ‖fcLeadingOperator Q N (Q u) I.2 - ε • L₀‖ ≤ M * J * ε ^ 2 := by
    have hb := hlead (Q u) hKu (I.2 - ε • S)
    rw [hlin] at hb
    exact hb.trans ((mul_le_mul_of_nonneg_left hΘ hM).trans_eq (by ring))
  have hremainder : ‖F - fcLeadingOperator Q N (Q u) I.2‖ ≤ C * P ^ 2 * ε ^ 2 := by
    have hb := htaylor (Q u) hKu I.1 I.2 hismall
    have hsq : ‖I‖ ^ 2 ≤ (P * ε) ^ 2 := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hi
    exact hb.trans ((mul_le_mul_of_nonneg_left hsq hC).trans_eq (by ring))
  have htotal : ‖F - ε • L₀‖ ≤ R * ε ^ 2 := by
    have heq : F - ε • L₀ = (F - fcLeadingOperator Q N (Q u) I.2) +
        (fcLeadingOperator Q N (Q u) I.2 - ε • L₀) := by abel
    rw [heq]
    exact (norm_add_le _ _).trans ((add_le_add hremainder hresponse).trans_eq (by dsimp only [R]; ring))
  rw [metricFCPoint_gradient_eq_finiteTerminal T hT f G H Q hr hG₀ hHc₀ hLr hH hF hG
    ε hε.ne' u hs.1 N]
  change ‖ε • F - ε ^ 2 • L₀‖ ≤ R * ε ^ 3
  rw [show ε • F - ε ^ 2 • L₀ = ε • (F - ε • L₀) by rw [smul_sub, smul_smul, pow_two],
    norm_smul, Real.norm_of_nonneg hε.le]
  exact (mul_le_mul_of_nonneg_left htotal hε.le).trans_eq (by ring)

end
end krylov.Functions
