import krylov.Functions.FCOwnCanonical

/-!
Article: main_krylov, thm:Htransfer, literal native FC response in original A₀ coordinates.
Use: retain the actual first-secant reference and true observed initial
gradient, construct its positive matrix and canonical metric, and obtain
the printed flag/tail response with a genuine compact-uniform function remainder.
Source: genuine native function transfer, actual matrix positivity and CG
stopping, real CFC inverse-root compactness and the exact spatial response dictionary.
-/

namespace krylov.Functions
noncomputable section
open Set Metric Matrix Finset krylov.Methods krylov.Reference krylov.Nonlinear krylov.Variation krylov.Secant
open scoped InnerProductSpace BigOperators NNReal Matrix.Norms.L2Operator
variable {n : ℕ}

/-- Actual full native FC has the literal printed compatible spatial response at its original first-secant reference, with a genuine compact-uniform little-o remainder.
Article: main_krylov, thm:Htransfer, original-A₀ canonical FC formula.
Proof: actual original-reference function transfer gives the true FC first
derivative. The original observed positive secant determines its genuine
matrix and full reference spectrum. Schwarz gives the real tensor symmetry;
the exact derivative/response dictionary and compact true inverse-root bound
transfer the actual remainder uniformly to the original canonical metric. -/
theorem metricFCPoint_own_spatial_leading_gradient
    (T : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (hT : T.symm.toContinuousLinearMap.IsSymmetric)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (Q : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (D : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hD : HasFDerivAt H D 0) {r : ℝ} (hr : 0 < r) (hG₀ : G 0 = 0) (hH₀ : H 0 = Q)
    (hHc₀ : coordinateDerivative T H 0 = ContinuousLinearMap.id ℝ _)
    {L : ℝ≥0} (hLr : (L : ℝ) * r ≤ 1 / 2)
    (hH : LipschitzOnWith L (coordinateDerivative T H) (closedBall 0 r))
    (hF : ∀ z, ‖T z‖ ≤ r → HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z, ‖T z‖ ≤ r → HasFDerivAt G (H z) z)
    (K : Set ((EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) × EuclideanSpace ℝ (Fin n)))
    (hK : IsCompact K)
    (hquad : ∀ z ∈ K, z.1.toLinearMap.IsSymmetric ∧
      (∀ v, v ≠ 0 → 0 < inner ℝ v (z.1 v)) ∧ ∀ i < n, CG.gradient z.1 z.2 i ≠ 0)
    (B : ℝ) (hB : 0 < B) :
    ∀ η : ℝ, 0 < η → ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∀ u, ‖u‖ ≤ B →
      let A := metricFCOperator T f G H fullMemory r (ε • u)
      let g := ε⁻¹ • G (ε • u)
      let base := physicalOperatorMatrix (A 0)
      (A 0, g) ∈ K → ∃ hb : base.PosDef,
      ‖cgOperator (metricRoot base)⁻¹ (G (metricFCPoint T f G fullMemory r (ε • u) n)) -
        ε ^ 2 • fullCycleResponse base g (range n) (ownFCCompatibleIncrements base hb D g)‖ ≤ η * ε ^ 2 := by
  intro η hη
  obtain ⟨M, hM, hmetric⟩ := own_inverseRoot_compact_bound K hK (fun z hz => ⟨(hquad z hz).1, (hquad z hz).2.1⟩)
  have hquad' : ∀ z ∈ K, z.1.toLinearMap.IsSymmetric ∧
      (∀ v, v ≠ 0 → 0 < inner ℝ v (z.1 v)) ∧
      ∀ i < Module.finrank ℝ (EuclideanSpace ℝ (Fin n)), CG.gradient z.1 z.2 i ≠ 0 := by
    intro z hz
    simpa only [finrank_euclideanSpace_fin] using hquad z hz
  obtain ⟨ε₀, hε₀, hbound⟩ := metricFCPoint_own_leading_gradient T hT f G H Q D hD hr hG₀ hH₀ hHc₀
    hLr hH hF hG K hK hquad' B hB (η / (M + 1)) (by positivity)
  refine ⟨ε₀, hε₀, ?_⟩
  intro ε hε he u hu
  dsimp only
  let A := metricFCOperator T f G H fullMemory r (ε • u)
  let g := ε⁻¹ • G (ε • u)
  let base := physicalOperatorMatrix (A 0)
  intro hKref
  have hb : base.PosDef := physicalOperatorMatrix_posDef (A 0) (hquad _ hKref).1 (hquad _ hKref).2.1
  have hoperator : cgOperator base = A 0 := physicalOperatorMatrix_operator _
  have hcount : referenceAtomCount base hb g = n := by
    apply referenceAtomCount_eq_of_full_nonstagnation base hb g
    rw [hoperator]
    exact (hquad _ hKref).2.2
  have hp := hbound ε hε he u hu hKref
  rw [finrank_euclideanSpace_fin] at hp
  have hsym v := genuine_third_slice_symmetric T f G H D hD hr hF hG v
  have hc := fcOwnCanonical_error_bound base hb D hsym g u hcount ε
    (G (metricFCPoint T f G fullMemory r (ε • u) n))
  dsimp only at hc
  rw [hoperator] at hc
  have hroot : ‖cgOperator (metricRoot base)⁻¹‖ ≤ M := hmetric (A 0, g) hKref
  refine ⟨hb, hc.trans ?_⟩
  have hco : M * (η / (M + 1)) ≤ η := by
    have heq : η / (M + 1) * (M + 1) = η := by field_simp
    have hn : 0 ≤ η / (M + 1) := by positivity
    nlinarith
  calc
    _ ≤ M * ‖G (metricFCPoint T f G fullMemory r (ε • u) n) - ε ^ 2 •
        fcLeadingOperator (A 0) n g (fun i => D (fcOwnReferenceMidpoint (A 0) g u i.val - fcOwnReferenceMidpoint (A 0) g u 0))‖ :=
      mul_le_mul_of_nonneg_right hroot (norm_nonneg _)
    _ ≤ M * (η / (M + 1) * ε ^ 2) := mul_le_mul_of_nonneg_left hp hM
    _ = (M * (η / (M + 1))) * ε ^ 2 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hco (sq_nonneg ε)

/-- Actual full native FC has the literal original-A₀ spatial response with a compact-uniform cubic remainder under a genuine Lipschitz third derivative.
Article: main_krylov, lem:cycle-transfer and thm:Htransfer, canonical O(e³).
Proof: the actual own-reference physical cubic remainder is already proved.
The genuine positive observed matrix, actual full CG spectrum and exact
spatial coefficient dictionary transport it through uniformly bounded true
inverse roots on the original compact reference family. -/
theorem metricFCPoint_own_spatial_cubic_remainder
    (T : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (hT : T.symm.toContinuousLinearMap.IsSymmetric)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (Q : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (D : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    {r : ℝ} (hr : 0 < r) (hG₀ : G 0 = 0) (hH₀ : H 0 = Q)
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
    (B : ℝ) (hB : 0 < B) :
    ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∀ u, ‖u‖ ≤ B →
      let A := metricFCOperator T f G H fullMemory r (ε • u)
      let g := ε⁻¹ • G (ε • u)
      let base := physicalOperatorMatrix (A 0)
      (A 0, g) ∈ K → ∃ hb : base.PosDef,
      ‖cgOperator (metricRoot base)⁻¹ (G (metricFCPoint T f G fullMemory r (ε • u) n)) -
        ε ^ 2 • fullCycleResponse base g (range n) (ownFCCompatibleIncrements base hb (D 0) g)‖ ≤ C * ε ^ 3 := by
  obtain ⟨M, hM, hmetric⟩ := own_inverseRoot_compact_bound K hK (fun z hz => ⟨(hquad z hz).1, (hquad z hz).2.1⟩)
  have hquad' : ∀ z ∈ K, z.1.toLinearMap.IsSymmetric ∧
      (∀ v, v ≠ 0 → 0 < inner ℝ v (z.1 v)) ∧
      ∀ i < Module.finrank ℝ (EuclideanSpace ℝ (Fin n)), CG.gradient z.1 z.2 i ≠ 0 := by
    intro z hz
    simpa only [finrank_euclideanSpace_fin] using hquad z hz
  obtain ⟨ε₀, R, hε₀, hR, hbound⟩ := metricFCPoint_own_cubic_remainder T hT f G H Q D hr hG₀ hH₀ hHc₀
    hLr hH hF hG hD hDlip K hK hquad' B hB
  refine ⟨ε₀, M * R, hε₀, mul_nonneg hM hR, ?_⟩
  intro ε hε he u hu
  dsimp only
  let A := metricFCOperator T f G H fullMemory r (ε • u)
  let g := ε⁻¹ • G (ε • u)
  let base := physicalOperatorMatrix (A 0)
  intro hKref
  have hb : base.PosDef := physicalOperatorMatrix_posDef (A 0) (hquad _ hKref).1 (hquad _ hKref).2.1
  have hoperator : cgOperator base = A 0 := physicalOperatorMatrix_operator _
  have hcount : referenceAtomCount base hb g = n := by
    apply referenceAtomCount_eq_of_full_nonstagnation base hb g
    rw [hoperator]
    exact (hquad _ hKref).2.2
  have hp := hbound ε hε he u hu hKref
  rw [finrank_euclideanSpace_fin] at hp
  have hD₀ : HasFDerivAt H (D 0) 0 := hD 0 (by simpa only [map_zero, norm_zero] using hr.le)
  have hsym v := genuine_third_slice_symmetric T f G H (D 0) hD₀ hr hF hG v
  have hc := fcOwnCanonical_error_bound base hb (D 0) hsym g u hcount ε
    (G (metricFCPoint T f G fullMemory r (ε • u) n))
  dsimp only at hc
  rw [hoperator] at hc
  have hroot : ‖cgOperator (metricRoot base)⁻¹‖ ≤ M := hmetric (A 0, g) hKref
  refine ⟨hb, hc.trans ?_⟩
  calc
    _ ≤ M * ‖G (metricFCPoint T f G fullMemory r (ε • u) n) - ε ^ 2 •
        fcLeadingOperator (A 0) n g (fun i => D 0 (fcOwnReferenceMidpoint (A 0) g u i.val - fcOwnReferenceMidpoint (A 0) g u 0))‖ :=
      mul_le_mul_of_nonneg_right hroot (norm_nonneg _)
    _ ≤ M * (R * ε ^ 3) := mul_le_mul_of_nonneg_left hp hM
    _ = _ := by ring

end
end krylov.Functions
