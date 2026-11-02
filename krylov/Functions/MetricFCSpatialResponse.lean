import krylov.Functions.FCLeadingCoordinates
import krylov.Functions.GenuineHessianSymmetry

/-!
Article: main_krylov, thm:Htransfer, native FC spatial leading-gradient formula.
Use: combine real local exact-search execution, genuine compact function
transfer, actual Schwarz symmetry and the established sharp CG flag response.
All metric coordinates are constructed from the actual positive Hessian.
Source: Appendix G and thm:A; the coefficient is the literal fullCycleResponse.
-/

namespace krylov.Functions
noncomputable section
open Set Metric Matrix Finset krylov.Methods krylov.Reference krylov.Nonlinear krylov.Variation krylov.Secant
open scoped InnerProductSpace BigOperators NNReal
variable {n : ℕ}

/-- The genuine canonical third-derivative slices at consecutive true quadratic reference midpoints.
Article: main_krylov, thm:Htransfer, compatible FC increments. -/
def fcCompatibleIncrements (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (D : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (u : EuclideanSpace ℝ (Fin n)) (l : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  physicalCanonicalMatrix base hb (D (fcReferenceMidpoint (cgOperator base) u (l + 1))) -
    physicalCanonicalMatrix base hb (D (fcReferenceMidpoint (cgOperator base) u l))

/-- The actual native compatible-tensor coefficient is exactly the printed spatial CG response.
Article: main_krylov, thm:Htransfer, ΣP_l T[ξ_l]v_l. -/
theorem fcTensorLeading_eq_fullCycleResponse (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (D : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hDsym : ∀ v, (D v).toLinearMap.IsSymmetric) (u : EuclideanSpace ℝ (Fin n))
    (hcount : referenceAtomCount base hb (cgOperator base u) = n) :
    cgOperator (metricRoot base)⁻¹ (fcTensorLeading (cgOperator base) D u) =
      fullCycleResponse base (cgOperator base u) (range n) (fcCompatibleIncrements base hb D u) := by
  unfold fcTensorLeading fcCompatibleIncrements
  convert! fcLeadingOperator_eq_fullCycleResponse base hb (cgOperator base u) hcount
    (fun i => D (fcReferenceMidpoint (cgOperator base) u i)) (fun i _ => hDsym _) using 1
  rw [finrank_euclideanSpace_fin]

/-- The actual physical native FC cycle has the printed compatible-tensor spatial leading gradient, uniformly on compact full reference families.
Article: main_krylov, thm:Htransfer, FC leading-gradient formula on functions.
Proof: construct the canonical metric from the true positive Hessian. Genuine
successive derivatives of the scalar objective imply the required symmetric
tensor slices by Schwarz. The proved actual native compact expansion and the
proved exact derivative/flag-response dictionary give the printed coefficient. -/
theorem metricFCPoint_spatial_leading_gradient
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (D : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hD : HasFDerivAt H D 0)
    {r : ℝ} (hr : 0 < r) (hG₀ : G 0 = 0) (hH₀ : H 0 = cgOperator base)
    {L : ℝ≥0} (hLr : (L : ℝ) * r ≤ 1 / 2)
    (hH : LipschitzOnWith L (coordinateDerivative (metricCoordinates base hb) H) (closedBall 0 r))
    (hF : ∀ z, ‖metricCoordinates base hb z‖ ≤ r → HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z, ‖metricCoordinates base hb z‖ ≤ r → HasFDerivAt G (H z) z)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K)
    (hcount : ∀ g ∈ K, referenceAtomCount base hb g = n) (B : ℝ) (hB : 0 < B) :
    ∀ η : ℝ, 0 < η → ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∀ u, ‖u‖ ≤ B → cgOperator base u ∈ K →
      ‖cgOperator (metricRoot base)⁻¹
          (G (metricFCPoint (metricCoordinates base hb) f G fullMemory r (ε • u) n)) -
        ε ^ 2 • fullCycleResponse base (cgOperator base u) (range n) (fcCompatibleIncrements base hb D u)‖ ≤ η * ε ^ 2 := by
  intro η hη
  let T := metricCoordinates base hb
  let J := ‖T.symm.toContinuousLinearMap‖
  have hJ : 0 ≤ J := norm_nonneg _
  obtain ⟨hQ, hpos⟩ := cgOperator_positive base hb
  have hpre : ∀ g ∈ K, ∀ i < Module.finrank ℝ (EuclideanSpace ℝ (Fin n)),
      CG.gradient (cgOperator base) g i ≠ 0 := by
    intro g hg i hi
    apply cg_nonstagnation_of_full_atoms base hb g (hcount g hg) i
    simpa only [finrank_euclideanSpace_fin] using hi
  obtain ⟨ε₀, hε₀, hbound⟩ := metricFCPoint_leading_gradient T
    (metricCoordinates_inverse_symmetric base hb) f G H (cgOperator base) D hD hr hG₀ hH₀
    (coordinateDerivative_metric_zero base hb H hH₀) hLr hH hF hG hQ hpos K hK hpre B hB
    (η / (J + 1)) (by positivity)
  refine ⟨ε₀, hε₀, ?_⟩
  intro ε hε he u hu hKu
  have hp := hbound ε hε he u hu hKu
  simp only [finrank_euclideanSpace_fin] at hp
  have hsym v := genuine_third_slice_symmetric T f G H D hD hr hF hG v
  have hcoeff := fcTensorLeading_eq_fullCycleResponse base hb D hsym u (hcount _ hKu)
  have hn := T.symm.toContinuousLinearMap.le_opNorm
    (G (metricFCPoint T f G fullMemory r (ε • u) n) - ε ^ 2 • fcTensorLeading (cgOperator base) D u)
  rw [map_sub, map_smul] at hn
  change ‖cgOperator (metricRoot base)⁻¹
      (G (metricFCPoint T f G fullMemory r (ε • u) n)) -
      ε ^ 2 • cgOperator (metricRoot base)⁻¹ (fcTensorLeading (cgOperator base) D u)‖ ≤ _ at hn
  rw [hcoeff] at hn
  apply hn.trans
  have heq : η / (J + 1) * (J + 1) = η := by field_simp
  have hm := mul_le_mul_of_nonneg_left hp hJ
  have hquot : 0 ≤ η / (J + 1) := div_nonneg hη.le (by positivity)
  have hco : J * (η / (J + 1)) ≤ η := by nlinarith
  change J * ‖G (metricFCPoint T f G fullMemory r (ε • u) n) -
    ε ^ 2 • fcTensorLeading (cgOperator base) D u‖ ≤ _
  apply hm.trans
  calc
    _ = (J * (η / (J + 1))) * ε ^ 2 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hco (sq_nonneg ε)

end
end krylov.Functions
