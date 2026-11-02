import krylov.Functions.RFCFCanonicalQuadratic

/-!
Article: main_krylov, prop:Fcycle(i), actual native canonical RFC-F expansion.
Use: the true returned scalar-function gradient has the genuine corrected
staircase/fresh-defect tensor coefficient in the actual minimizer metric.
Source: proved native physical tensor transfer and exact canonical raw-model
compression, including the real half-step value diagonal.
-/
namespace krylov.Functions
noncomputable section
open Set Metric Matrix krylov.Methods krylov.Reference krylov.Nonlinear krylov.Secant
open scoped InnerProductSpace NNReal Matrix.Norms.L2Operator
variable {k : ℕ}

set_option maxHeartbeats 800000 in
/-- The true native RFC terminal gradient has the printed compatible tensor
corrected staircase product in the actual minimizer metric, uniformly over compact
full-atom reference families. Article: main_krylov, prop:Fcycle(i). -/
theorem metricRFCFPoint_spatial_leading_gradient
    (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef) (hk : 0<k)
    (f : EuclideanSpace ℝ (Fin (k+1)) → ℝ)
    (G : EuclideanSpace ℝ (Fin (k+1)) → EuclideanSpace ℝ (Fin (k+1)))
    (H : EuclideanSpace ℝ (Fin (k+1)) → EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1)))
    (D : EuclideanSpace ℝ (Fin (k+1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1)))
    (hD : HasFDerivAt H D 0)
    {r : ℝ} (hr : 0<r) (hG₀ : G 0=0) (hH₀ : H 0=cgOperator base)
    {L : ℝ≥0} (hLr : (L : ℝ)*r≤1/2)
    (hH : LipschitzOnWith L (coordinateDerivative (metricCoordinates base hb) H) (closedBall 0 r))
    (hF : ∀ z, ‖metricCoordinates base hb z‖≤r → HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z, ‖metricCoordinates base hb z‖≤r → HasFDerivAt G (H z) z)
    (K : Set (EuclideanSpace ℝ (Fin (k+1)))) (hK : IsCompact K)
    (hcount : ∀ g∈K, referenceAtomCount base hb g=k+1)
    (R : ℝ) (hR : 0<R) :
    ∀ η : ℝ, 0<η → ∃ ε₀ : ℝ, 0<ε₀ ∧ ∀ ε : ℝ, 0<ε → ε<ε₀ →
      ∀ u : EuclideanSpace ℝ (Fin (k+1)), ‖u‖≤R → cgOperator base u∈K →
      ‖cgOperator (metricRoot base)⁻¹
          (G (rfcFPoint (metricCoordinates base hb) f G r (ε • u) k))+
        ε^3 • rfcFTensorCanonicalCoefficient base hb D u‖≤η*ε^3 := by
  have hpre : ∀ g∈K, ∀ i≤k, CG.gradient (cgOperator base) g i≠0 := by
    intro g hg i hi
    exact cg_nonstagnation_of_full_atoms base hb g (hcount g hg) i (by omega)
  let J := ‖(metricCoordinates base hb).symm.toContinuousLinearMap‖
  have hJ : 0≤J := norm_nonneg _
  intro η hη
  obtain ⟨ep,hep,hbound⟩ := nativeRFCF_tensor_cubic_remainder base hb hk (metricCoordinates base hb)
    (metricCoordinates_inverse_symmetric base hb) f G H D hD hr hG₀ hH₀
    (coordinateDerivative_metric_zero base hb H hH₀) hLr hH hF hG K hK hpre R hR
    (η/(J+1)) (by positivity)
  refine ⟨ep,hep,?_⟩
  intro ε hε he u hu hKu
  have hp := hbound ε hε he u hu hKu
  have hc := rfcFTensorPhysicalCoefficient_eq_canonical base hb D u (by rw [hcount _ hKu])
  have hn := (metricCoordinates base hb).symm.toContinuousLinearMap.le_opNorm
    (G (rfcFPoint (metricCoordinates base hb) f G r (ε • u) k)+
      ε^3 • rfcFTensorPhysicalCoefficient base D u)
  rw [map_add,map_smul] at hn
  change ‖cgOperator (metricRoot base)⁻¹
      (G (rfcFPoint (metricCoordinates base hb) f G r (ε • u) k))+
      ε^3 • cgOperator (metricRoot base)⁻¹ (rfcFTensorPhysicalCoefficient base D u)‖≤_ at hn
  rw [hc] at hn
  change ‖_+ε^3 • rfcFTensorCanonicalCoefficient base hb D u‖≤_ at hn
  have hcoef : J*(η/(J+1))≤η := by
    have hh : η/(J+1)*(J+1)=η := by field_simp
    nlinarith only [hh,div_nonneg hη.le (by positivity : 0≤J+1)]
  apply hn.trans
  change J*‖G (rfcFPoint (metricCoordinates base hb) f G r (ε • u) k)+
    ε^3 • rfcFTensorPhysicalCoefficient base D u‖≤η*ε^3
  calc
    _ ≤ J*(η/(J+1)*ε^3) := mul_le_mul_of_nonneg_left hp hJ
    _ = (J*(η/(J+1)))*ε^3 := by ring
    _ ≤ η*ε^3 := mul_le_mul_of_nonneg_right hcoef (pow_nonneg hε.le 3)

end
end krylov.Functions
