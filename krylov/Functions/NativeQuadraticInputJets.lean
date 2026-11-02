import krylov.Functions.MetricFCInputJet
import krylov.Functions.NativeRFCInputJet
import krylov.Functions.MetricFCQuadraticJet
import krylov.Functions.NormalizedGradientQuadratic

/-!
Article: main_krylov, lem:cycle-transfer, complete actual quadratic input jets.
Use: derive all actual independent source coordinates to order O(e²), from
primitive genuine Lipschitz third derivatives. No source jet is a hypothesis.
-/
namespace krylov.Functions
noncomputable section
open Set Metric krylov.Methods krylov.Nonlinear krylov.Reference
open scoped InnerProductSpace NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

/-- The complete genuine native source has a uniform quadratic jet
remainder under actual Lipschitz third derivatives. Article: lem:cycle-transfer. -/
theorem metricFCInput_reference_jet_quadratic (T : E ≃L[ℝ] E)
    (hT : T.symm.toContinuousLinearMap.IsSymmetric)
    (f : E → ℝ) (G : E → E) (H : E → E →L[ℝ] E) (Q : E →L[ℝ] E)
    (D : E → E →L[ℝ] E →L[ℝ] E)
    {r : ℝ} (hr : 0<r) (hG₀ : G 0=0) (hH₀ : H 0=Q)
    (hHc₀ : coordinateDerivative T H 0=ContinuousLinearMap.id ℝ E)
    {L L₃ : ℝ≥0} (hLr : (L : ℝ)*r≤1/2)
    (hH : LipschitzOnWith L (coordinateDerivative T H) (closedBall 0 r))
    (hD : ∀ z : E, ‖T z‖≤r → HasFDerivAt H (D z) z)
    (hDlip : LipschitzOnWith L₃ D (T ⁻¹' closedBall (0:E) r))
    (hF : ∀ z : E, ‖T z‖≤r → HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z : E, ‖T z‖≤r → HasFDerivAt G (H z) z)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v))
    (N : ℕ) (K : Set E) (hK : IsCompact K)
    (hpre : ∀ g∈K, ∀ i<N, CG.gradient Q g i≠0)
    (B : ℝ) (hB : 0<B) :
    ∃ ε₀ C : ℝ, 0<ε₀ ∧ 0≤C ∧ ∀ ε : ℝ, 0<ε → ε<ε₀ →
      ∀ u : E, ‖u‖≤B → Q u∈K →
        ‖metricFCInput T f G H Q r ε u N-ε • metricFCReferenceInputJet Q (D 0) u N‖≤C*ε^2 := by
  obtain ⟨eg,Cg,heg,hCg,hgj⟩ := normalizedGradient_reference_quadratic_jet T G H Q D
    hr hG₀ hH₀ hG hD hDlip B hB
  obtain ⟨ea,Ca,hea,hCa,haj⟩ := metricFCOperator_reference_quadratic_jet T hT f G H Q D
    hr hG₀ hH₀ hHc₀ hLr hH hF hG hD hDlip hQ hpos N K hK hpre B hB
  refine ⟨min eg ea,Cg+Ca,lt_min heg hea,by positivity,?_⟩
  intro ε hε he u hu hKu
  change max ‖ε⁻¹ • G (ε • u)-Q u-ε • ((1/2 : ℝ) • D 0 u u)‖
    ‖fun i : Fin N => metricFCOperator T f G H fullMemory r (ε • u) i.val-Q-
      ε • D 0 (fcReferenceMidpoint Q u i.val)‖≤(Cg+Ca)*ε^2
  apply max_le
  · exact (hgj ε hε (he.trans_le (min_le_left _ _)) u hu).trans
      (by nlinarith only [mul_nonneg hCa (sq_nonneg ε)])
  · apply (pi_norm_le_iff_of_nonneg (by positivity : 0≤(Cg+Ca)*ε^2)).mpr
    intro i
    exact (haj ε hε (he.trans_le (min_le_right _ _)) u hu hKu i.val i.isLt).trans
      (by nlinarith only [mul_nonneg hCg.le (sq_nonneg ε)])

/-- The complete genuine native source has a uniform quadratic jet
remainder under actual Lipschitz third derivatives. Article: lem:cycle-transfer. -/
theorem nativeRFCInput_reference_jet_quadratic (T : E ≃L[ℝ] E)
    (hT : T.symm.toContinuousLinearMap.IsSymmetric)
    (f : E → ℝ) (G : E → E) (H : E → E →L[ℝ] E) (Q : E →L[ℝ] E)
    (D : E → E →L[ℝ] E →L[ℝ] E)
    {r : ℝ} (hr : 0<r) (hG₀ : G 0=0) (hH₀ : H 0=Q)
    (hHc₀ : coordinateDerivative T H 0=ContinuousLinearMap.id ℝ E)
    {L L₃ : ℝ≥0} (hLr : (L : ℝ)*r≤1/2)
    (hH : LipschitzOnWith L (coordinateDerivative T H) (closedBall 0 r))
    (hD : ∀ z : E, ‖T z‖≤r → HasFDerivAt H (D z) z)
    (hDlip : LipschitzOnWith L₃ D (T ⁻¹' closedBall (0:E) r))
    (hF : ∀ z : E, ‖T z‖≤r → HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z : E, ‖T z‖≤r → HasFDerivAt G (H z) z)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v))
    (N : ℕ) (K : Set E) (hK : IsCompact K)
    (hpre : ∀ g∈K, ∀ i<N, CG.gradient Q g i≠0)
    (B : ℝ) (hB : 0<B) :
    ∃ ε₀ C : ℝ, 0<ε₀ ∧ 0≤C ∧ ∀ ε : ℝ, 0<ε → ε<ε₀ →
      ∀ u : E, ‖u‖≤B → Q u∈K →
        ‖nativeRFCInput T f G H Q r ε u N-ε • nativeRFCReferenceInputJet Q (D 0) u N‖≤C*ε^2 := by
  obtain ⟨eg,Cg,heg,hCg,hgj⟩ := normalizedGradient_reference_quadratic_jet T G H Q D
    hr hG₀ hH₀ hG hD hDlip B hB
  obtain ⟨ea,Ca,hea,hCa,haj⟩ := nativeRFC_reference_operator_jets_quadratic T hT f G H Q D
    hr hG₀ hH₀ hHc₀ hLr hH hD hDlip hF hG hQ hpos N K hK hpre B hB
  refine ⟨min eg ea,Cg+Ca,lt_min heg hea,by positivity,?_⟩
  intro ε hε he u hu hKu
  change max ‖ε⁻¹ • G (ε • u)-Q u-ε • ((1/2 : ℝ) • D 0 u u)‖
    (max ‖fun i : Fin N => rfcFunctionSearchOperator T f G H fullMemory r (ε • u) i.val-Q-
      ε • D 0 (rfcReferenceSearchMidpoint Q u i.val)‖
      ‖fun i : Fin N => rfcFunctionCorrectionOperator T f G H fullMemory r (ε • u) i.val-Q-
      ε • D 0 (fcQuadraticReferencePoint Q u (i.val+1))‖)≤(Cg+Ca)*ε^2
  apply max_le
  · exact (hgj ε hε (he.trans_le (min_le_left _ _)) u hu).trans
      (by nlinarith only [mul_nonneg hCa.le (sq_nonneg ε)])
  · apply max_le
    · apply (pi_norm_le_iff_of_nonneg (by positivity : 0≤(Cg+Ca)*ε^2)).mpr
      intro i
      exact (haj ε hε (he.trans_le (min_le_right _ _)) u hu hKu i.val i.isLt).1.trans
        (by nlinarith only [mul_nonneg hCg.le (sq_nonneg ε)])
    · apply (pi_norm_le_iff_of_nonneg (by positivity : 0≤(Cg+Ca)*ε^2)).mpr
      intro i
      exact (haj ε hε (he.trans_le (min_le_right _ _)) u hu hKu i.val i.isLt).2.trans
        (by nlinarith only [mul_nonneg hCg.le (sq_nonneg ε)])

end
end krylov.Functions
