import krylov.Functions.MetricFCLeadingSource

/-!
Article: main_krylov, lem:cycle-transfer and thm:Htransfer, native FC leading gradient.
Use: the actual physical objective, true exact searches and real measured
secants produce a compact-uniform degree-two terminal-gradient expansion.
Its coefficient is the true first derivative of the actual FC operator map,
evaluated on compatible slices of the one genuine third derivative.
Source: Appendix G; no terminal remainder or query bound is an input field.
-/

/-!
Article: krylov, Proposition E.7 [thm:Htransfer].

Actual FC/RFC query secants have compatible slices of the same genuine scalar third derivative;
the resulting spatial response degrees are two and three.
C3 supplies a compact-uniform little-o remainder; Lipschitz D3 yields the next-power remainder.
Canonical and physical metrics are related by the explicit metric coordinates.
-/

namespace krylov.Functions
noncomputable section
open Set Metric krylov.Methods krylov.Reference krylov.Nonlinear
open scoped InnerProductSpace NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

/-- The actual FC degree-two function coefficient: the genuine operator derivative on the genuine reference-midpoint tensor slices.
Article: main_krylov, thm:Htransfer, the FC leading gradient. -/
def fcTensorLeading (Q : E →L[ℝ] E) (D : E →L[ℝ] E →L[ℝ] E) (u : E) : E :=
  fcLeadingOperator Q (Module.finrank ℝ E) (Q u)
    (fun i => D (fcReferenceMidpoint Q u i.val))

/-- The actual full native FC cycle has its compact-uniform compatible-tensor degree-two leading gradient.
Article: main_krylov, thm:Htransfer and lem:cycle-transfer, genuine FC function substitution.
Proof: localize all actual queries from the original objective. Identify the
real terminal gradient with the homogeneous finite FC map at its actual
normalized inputs. Its true quadratic-reference slice kills initial-gradient
drift. Substitute the derived compatible first jets of all true Hessian secants
in the genuine compact first Taylor polynomial; all errors are uniform. -/
theorem metricFCPoint_leading_gradient (T : E ≃L[ℝ] E)
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
    (K : Set E) (hK : IsCompact K)
    (hpre : ∀ g ∈ K, ∀ i < Module.finrank ℝ E, CG.gradient Q g i ≠ 0)
    (B : ℝ) (hB : 0 < B) :
    ∀ η : ℝ, 0 < η → ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∀ u : E, ‖u‖ ≤ B → Q u ∈ K →
      ‖G (metricFCPoint T f G fullMemory r (ε • u) (Module.finrank ℝ E)) -
        ε ^ 2 • fcTensorLeading Q D u‖ ≤ η * ε ^ 2 := by
  intro η hη
  let N := Module.finrank ℝ E
  obtain ⟨δ, C, M, hδ, hC, hM, hlead, htaylor⟩ := compact_fc_leading_operator Q hQ hpos K hK hpre
  obtain ⟨εs, P, hεs, hP, hsource⟩ := metricFCInput_bound T hT f G H Q hr hG₀ hH₀ hHc₀ hLr hH hF hG B hB
  let χ := η / (2 * (M + 1))
  have hχ : 0 < χ := by dsimp only [χ]; positivity
  obtain ⟨εj, hεj, hjet⟩ := metricFCOperator_reference_jet T hT f G H Q D hD hr hG₀ hH₀ hHc₀
    hLr hH hF hG hQ hpos N K hK hpre B hB χ hχ
  let Z := C * P ^ 2
  have hZ : 0 ≤ Z := by dsimp only [Z]; positivity
  let ε₀ := min εs (min εj (min (δ / (P + 1)) (η / (2 * (Z + 1)))))
  have hε₀ : 0 < ε₀ := by dsimp only [ε₀]; positivity
  refine ⟨ε₀, hε₀, ?_⟩
  intro ε hε he u hu hKu
  let I := metricFCInput T f G H Q r ε u N
  let S : Fin N → E →L[ℝ] E := fun i => D (fcReferenceMidpoint Q u i.val)
  let F := fcFiniteTerminal Q N (Q u + I.1, I.2)
  let L₀ := fcLeadingOperator Q N (Q u) S
  have hs := hsource ε hε (he.trans_le (min_le_left _ _)) u hu
  have hi : ‖I‖ ≤ P * ε := hs.2 N
  have hismall : ‖I‖ ≤ δ := by
    have he' := (lt_div_iff₀ (by positivity : 0 < P + 1)).mp
      (he.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
    exact hi.trans (by nlinarith)
  have hΘ : ‖I.2 - ε • S‖ ≤ χ * ε := by
    apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ χ * ε)).mpr
    intro i
    exact hjet ε hε (he.trans_le ((min_le_right _ _).trans (min_le_left _ _))) u hu hKu i.val i.isLt
  have hlin : fcLeadingOperator Q N (Q u) (I.2 - ε • S) =
      fcLeadingOperator Q N (Q u) I.2 - ε • L₀ := by
    change (fderiv ℝ (fcFiniteTerminal Q N) (Q u, 0)) (0, I.2 - ε • S) = _
    rw [show ((0 : E), I.2 - ε • S) = (0, I.2) - ε • (0, S) by ext <;> simp,
      map_sub, map_smul]
    rfl
  have hresponse : ‖fcLeadingOperator Q N (Q u) I.2 - ε • L₀‖ ≤ η / 2 * ε := by
    have hb := hlead (Q u) hKu (I.2 - ε • S)
    rw [hlin] at hb
    apply hb.trans
    have hmχ : M * χ ≤ η / 2 := by
      have heq : χ * (2 * (M + 1)) = η := by dsimp only [χ]; field_simp
      nlinarith
    exact (mul_le_mul_of_nonneg_left hΘ hM).trans (by nlinarith [mul_le_mul_of_nonneg_right hmχ hε.le])
  have hremainder : ‖F - fcLeadingOperator Q N (Q u) I.2‖ ≤ η / 2 * ε := by
    have hb := htaylor (Q u) hKu I.1 I.2 hismall
    apply hb.trans
    have hsq : ‖I‖ ^ 2 ≤ (P * ε) ^ 2 := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hi
    have he' := (lt_div_iff₀ (by positivity : 0 < 2 * (Z + 1))).mp
      (he.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
    have hmul := mul_le_mul_of_nonneg_left hsq hC
    change C * ‖I‖ ^ 2 ≤ _
    calc
      _ ≤ C * (P * ε) ^ 2 := hmul
      _ = Z * ε ^ 2 := by dsimp only [Z]; ring
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right he'.le hε.le]
  have htotal : ‖F - ε • L₀‖ ≤ η * ε := by
    have heq : F - ε • L₀ = (F - fcLeadingOperator Q N (Q u) I.2) +
        (fcLeadingOperator Q N (Q u) I.2 - ε • L₀) := by abel
    rw [heq]
    exact (norm_add_le _ _).trans ((add_le_add hremainder hresponse).trans_eq (by ring))
  rw [metricFCPoint_gradient_eq_finiteTerminal T hT f G H Q hr hG₀ hHc₀ hLr hH hF hG
    ε hε.ne' u hs.1 N]
  change ‖ε • F - ε ^ 2 • L₀‖ ≤ η * ε ^ 2
  rw [show ε • F - ε ^ 2 • L₀ = ε • (F - ε • L₀) by rw [smul_sub, smul_smul, pow_two],
    norm_smul, Real.norm_of_nonneg hε.le]
  exact (mul_le_mul_of_nonneg_left htotal hε.le).trans_eq (by ring)

end
end krylov.Functions
