import krylov.Functions.NativeRFCOriginalReference
import krylov.Functions.NativeNormalizedReferences

/-!
Article: main_krylov, s7:N and thm:Htransfer, literal normalized RFC hypotheses.
Use: retain the full printed original first-secant tensor coefficient while
requiring compactness only of the actual normalized observed pairs.
No frozen full-reference set or physical compact family is assumed.
-/
namespace krylov.Functions
noncomputable section
open Set Metric Matrix krylov.Methods krylov.Reference krylov.Nonlinear krylov.Secant
open scoped InnerProductSpace NNReal Matrix.Norms.L2Operator
variable {k : ℕ}

/-- The literal normalized-reference native RFC tensor formula. Article:
main_krylov, s7:N and thm:Htransfer. -/
theorem metricRFCPoint_normalized_spatial_leading_gradient
    (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef) (hk : 0<k)
    (T : EuclideanSpace ℝ (Fin (k+1)) ≃L[ℝ] EuclideanSpace ℝ (Fin (k+1)))
    (hT : T.symm.toContinuousLinearMap.IsSymmetric)
    (f : EuclideanSpace ℝ (Fin (k+1)) → ℝ)
    (G : EuclideanSpace ℝ (Fin (k+1)) → EuclideanSpace ℝ (Fin (k+1)))
    (H : EuclideanSpace ℝ (Fin (k+1)) → EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1)))
    (D : EuclideanSpace ℝ (Fin (k+1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1)))
    (hD : HasFDerivAt H D 0)
    {r : ℝ} (hr : 0<r) (hG₀ : G 0=0) (hH₀ : H 0=cgOperator base)
    (hHc₀ : coordinateDerivative T H 0=ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin (k+1))))
    {L : ℝ≥0} (hLr : (L : ℝ)*r≤1/2)
    (hH : LipschitzOnWith L (coordinateDerivative T H) (closedBall 0 r))
    (hF₀ : ∀ z, ‖T z‖≤r → HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z, ‖T z‖≤r → HasFDerivAt G (H z) z)

    (K : Set ((EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1))) ×
      EuclideanSpace ℝ (Fin (k+1)))) (hK : IsCompact K)
    (hquad : ∀ z∈K, z.1.toLinearMap.IsSymmetric ∧
      (∀ w, w≠0 → 0 < inner ℝ w (z.1 w)) ∧ ∀ i<k+1, CG.gradient z.1 z.2 i≠0) :
    ∀ η : ℝ, 0<η → ∃ ε₀ : ℝ, 0<ε₀ ∧ ∀ ε : ℝ, 0<ε → ε<ε₀ →
      ∀ u : EuclideanSpace ℝ (Fin (k+1)), ‖u‖=1 →
      let A₀ := rfcFunctionSearchOperator T f G H fullMemory r (ε • u) 0
      let b := physicalOperatorMatrix A₀
      let g := ε⁻¹ • G (ε • u)
      normalizedReference A₀ (G (ε • u))∈K → ∃ hbown : b.PosDef,
      ‖cgOperator (metricRoot b)⁻¹
          (G (rfcFunctionPoint T f G fullMemory r (ε • u) (k+1)))+
        ε^3 • rfcOwnTensorCanonicalCoefficient b hbown D g‖≤η*ε^3 := by
  obtain ⟨es,hes,P,hP,hq,hcover⟩ := nativeRFC_normalized_reference_compact T hT f G H (cgOperator base)
    (cgOperator_positive base hb).2 hr hG₀ hH₀ hHc₀ hLr hH hF₀ hG (k+1) K hK hquad
  intro η hη
  obtain ⟨et,het,hbound⟩ := metricRFCPoint_original_spatial_leading_gradient base hb hk T hT f G H D hD
    hr hG₀ hH₀ hHc₀ hLr hH hF₀ hG 1 (by norm_num) P hP hq η hη
  refine ⟨min es et,lt_min hes het,?_⟩
  intro ε hε he u hu
  dsimp only
  intro hn
  exact hbound ε hε (he.trans_le (min_le_right _ _)) u hu.le
    (hcover ε hε (he.trans_le (min_le_left _ _)) u hu hn)

/-- The literal normalized-reference native RFC tensor formula. Article:
main_krylov, s7:N and thm:Htransfer. -/
theorem metricRFCPoint_normalized_spatial_quartic_remainder
    (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef) (hk : 0<k)
    (T : EuclideanSpace ℝ (Fin (k+1)) ≃L[ℝ] EuclideanSpace ℝ (Fin (k+1)))
    (hT : T.symm.toContinuousLinearMap.IsSymmetric)
    (f : EuclideanSpace ℝ (Fin (k+1)) → ℝ)
    (G : EuclideanSpace ℝ (Fin (k+1)) → EuclideanSpace ℝ (Fin (k+1)))
    (H : EuclideanSpace ℝ (Fin (k+1)) → EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1)))
    (D : EuclideanSpace ℝ (Fin (k+1)) → EuclideanSpace ℝ (Fin (k+1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1)))
    {r : ℝ} (hr : 0<r) (hG₀ : G 0=0) (hH₀ : H 0=cgOperator base)
    (hHc₀ : coordinateDerivative T H 0=ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin (k+1))))
    {L L₃ : ℝ≥0} (hLr : (L : ℝ)*r≤1/2)
    (hH : LipschitzOnWith L (coordinateDerivative T H) (closedBall 0 r))
    (hD : ∀ z, ‖T z‖≤r → HasFDerivAt H (D z) z)
    (hDlip : LipschitzOnWith L₃ D (T ⁻¹' closedBall 0 r))
    (hF₀ : ∀ z, ‖T z‖≤r → HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z, ‖T z‖≤r → HasFDerivAt G (H z) z)
    (K : Set ((EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1))) ×
      EuclideanSpace ℝ (Fin (k+1)))) (hK : IsCompact K)
    (hquad : ∀ z∈K, z.1.toLinearMap.IsSymmetric ∧
      (∀ w, w≠0 → 0 < inner ℝ w (z.1 w)) ∧ ∀ i<k+1, CG.gradient z.1 z.2 i≠0) :
    ∃ ε₀ C : ℝ, 0<ε₀ ∧ 0<C ∧ ∀ ε : ℝ, 0<ε → ε<ε₀ →
      ∀ u : EuclideanSpace ℝ (Fin (k+1)), ‖u‖=1 →
      let A₀ := rfcFunctionSearchOperator T f G H fullMemory r (ε • u) 0
      let b := physicalOperatorMatrix A₀
      let g := ε⁻¹ • G (ε • u)
      normalizedReference A₀ (G (ε • u))∈K → ∃ hbown : b.PosDef,
      ‖cgOperator (metricRoot b)⁻¹
          (G (rfcFunctionPoint T f G fullMemory r (ε • u) (k+1)))+
        ε^3 • rfcOwnTensorCanonicalCoefficient b hbown (D 0) g‖≤C*ε^4 := by
  obtain ⟨es,hes,P,hP,hq,hcover⟩ := nativeRFC_normalized_reference_compact T hT f G H (cgOperator base)
    (cgOperator_positive base hb).2 hr hG₀ hH₀ hHc₀ hLr hH hF₀ hG (k+1) K hK hquad
  obtain ⟨et,C,het,hC,hbound⟩ := metricRFCPoint_original_spatial_quartic_remainder base hb hk T hT f G H D
    hr hG₀ hH₀ hHc₀ hLr hH hD hDlip hF₀ hG 1 (by norm_num) P hP hq
  refine ⟨min es et,C,lt_min hes het,hC,?_⟩
  intro ε hε he u hu
  dsimp only
  intro hn
  exact hbound ε hε (he.trans_le (min_le_right _ _)) u hu.le
    (hcover ε hε (he.trans_le (min_le_left _ _)) u hu hn)

end
end krylov.Functions
