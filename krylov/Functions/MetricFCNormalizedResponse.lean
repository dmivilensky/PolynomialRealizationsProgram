import krylov.Functions.MetricFCOwnSpatialResponse
import krylov.Functions.NativeNormalizedReferences

/-!
Article: main_krylov, s7:N and thm:Htransfer, literal normalized FC hypotheses.
Use: retain the printed original first-secant spatial coefficient while
requiring compactness only of (A₀/‖A₀‖,g₀/‖g₀‖). Both physical scales and the
full physical compact family are derived from the actual scalar objective.
-/
namespace krylov.Functions
noncomputable section
open Set Metric Matrix Finset krylov.Methods krylov.Reference krylov.Nonlinear krylov.Variation krylov.Secant
open scoped InnerProductSpace BigOperators NNReal Matrix.Norms.L2Operator
variable {n : ℕ} [NeZero n]

/-- The literal normalized-reference native FC spatial formula. All auxiliary
physical compactness is derived. Article: main_krylov, s7:N and thm:Htransfer. -/
theorem metricFCPoint_normalized_spatial_leading_gradient
    (T : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (hT : T.symm.toContinuousLinearMap.IsSymmetric)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (Q : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (D : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hD : HasFDerivAt H D 0) {r : ℝ} (hr : 0 < r) (hG₀ : G 0 = 0) (hH₀ : H 0 = Q)
    (hpos : ∀ v, v≠0 → 0 < inner ℝ v (Q v))
    (hHc₀ : coordinateDerivative T H 0 = ContinuousLinearMap.id ℝ _)
    {L : ℝ≥0} (hLr : (L : ℝ) * r ≤ 1 / 2)
    (hH : LipschitzOnWith L (coordinateDerivative T H) (closedBall 0 r))
    (hF : ∀ z, ‖T z‖ ≤ r → HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z, ‖T z‖ ≤ r → HasFDerivAt G (H z) z)
    (K : Set ((EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) × EuclideanSpace ℝ (Fin n)))
    (hK : IsCompact K)
    (hquad : ∀ z ∈ K, z.1.toLinearMap.IsSymmetric ∧
      (∀ v, v ≠ 0 → 0 < inner ℝ v (z.1 v)) ∧ ∀ i < n, CG.gradient z.1 z.2 i ≠ 0)
    :
    ∀ η : ℝ, 0 < η → ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∀ u, ‖u‖=1 →
      let A := metricFCOperator T f G H fullMemory r (ε • u)
      let g := ε⁻¹ • G (ε • u)
      let base := physicalOperatorMatrix (A 0)
      normalizedReference (A 0) (G (ε • u)) ∈ K → ∃ hb : base.PosDef,
      ‖cgOperator (metricRoot base)⁻¹ (G (metricFCPoint T f G fullMemory r (ε • u) n)) -
        ε ^ 2 • fullCycleResponse base g (range n) (ownFCCompatibleIncrements base hb D g)‖ ≤ η * ε ^ 2 := by
  obtain ⟨es,hes,P,hP,hq,hcover⟩ := metricFC_normalized_reference_compact T hT f G H Q hpos
    hr hG₀ hH₀ hHc₀ hLr hH hF hG n K hK hquad
  intro η hη
  obtain ⟨et,het,hb⟩ := metricFCPoint_own_spatial_leading_gradient T hT f G H Q D hD
    hr hG₀ hH₀ hHc₀ hLr hH hF hG P hP hq 1 (by norm_num) η hη
  refine ⟨min es et,lt_min hes het,?_⟩
  intro ε hε he u hu
  dsimp only
  intro hn
  exact hb ε hε (he.trans_le (min_le_right _ _)) u hu.le
    (hcover ε hε (he.trans_le (min_le_left _ _)) u hu hn)

/-- The literal normalized-reference native FC spatial formula. All auxiliary
physical compactness is derived. Article: main_krylov, s7:N and thm:Htransfer. -/
theorem metricFCPoint_normalized_spatial_cubic_remainder
    (T : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (hT : T.symm.toContinuousLinearMap.IsSymmetric)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (Q : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (D : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    {r : ℝ} (hr : 0 < r) (hG₀ : G 0 = 0) (hH₀ : H 0 = Q)
    (hpos : ∀ v, v≠0 → 0 < inner ℝ v (Q v))
    (hHc₀ : coordinateDerivative T H 0 = ContinuousLinearMap.id ℝ _)
    {L L₃ : ℝ≥0} (hLr : (L : ℝ) * r ≤ 1 / 2)
    (hH : LipschitzOnWith L (coordinateDerivative T H) (closedBall 0 r))
    (hF : ∀ z, ‖T z‖ ≤ r → HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z, ‖T z‖ ≤ r → HasFDerivAt G (H z) z)
    (hD : ∀ z, ‖T z‖ ≤ r → HasFDerivAt H (D z) z)
    (hDlip : LipschitzOnWith L₃ D (T ⁻¹' closedBall (0 : EuclideanSpace ℝ (Fin n)) r))
    (K : Set ((EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) × EuclideanSpace ℝ (Fin n)))
    (hK : IsCompact K)
    (hquad : ∀ z ∈ K, z.1.toLinearMap.IsSymmetric ∧
      (∀ v, v ≠ 0 → 0 < inner ℝ v (z.1 v)) ∧ ∀ i < n, CG.gradient z.1 z.2 i ≠ 0)
    :
    ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∀ u, ‖u‖=1 →
      let A := metricFCOperator T f G H fullMemory r (ε • u)
      let g := ε⁻¹ • G (ε • u)
      let base := physicalOperatorMatrix (A 0)
      normalizedReference (A 0) (G (ε • u)) ∈ K → ∃ hb : base.PosDef,
      ‖cgOperator (metricRoot base)⁻¹ (G (metricFCPoint T f G fullMemory r (ε • u) n)) -
        ε ^ 2 • fullCycleResponse base g (range n) (ownFCCompatibleIncrements base hb (D 0) g)‖ ≤ C * ε ^ 3 := by
  obtain ⟨es,hes,P,hP,hq,hcover⟩ := metricFC_normalized_reference_compact T hT f G H Q hpos
    hr hG₀ hH₀ hHc₀ hLr hH hF hG n K hK hquad
  obtain ⟨et,C,het,hC,hb⟩ := metricFCPoint_own_spatial_cubic_remainder T hT f G H Q D
    hr hG₀ hH₀ hHc₀ hLr hH hF hG hD hDlip P hP hq 1 (by norm_num)
  refine ⟨min es et,C,lt_min hes het,hC,?_⟩
  intro ε hε he u hu
  dsimp only
  intro hn
  exact hb ε hε (he.trans_le (min_le_right _ _)) u hu.le
    (hcover ε hε (he.trans_le (min_le_left _ _)) u hu hn)

end
end krylov.Functions
