import krylov.Functions.NativeRFCTensorTransfer

/-!
Article: main_krylov, thm:Htransfer, native RFC compatible tensor formula.
Use: identify the real-function cubic coefficient with the printed canonical
staircase/fresh-defect product at the true quadratic midpoint increments.
Source: the exact physical/canonical response dictionary and elementary
reference-node telescoping; the common first-secant drift cancels exactly.
-/
namespace krylov.Functions
noncomputable section
open Set Metric Matrix krylov.Methods krylov.Reference krylov.Nonlinear krylov.Correction
  krylov.Variation krylov.Secant krylov.Envelope
open scoped InnerProductSpace NNReal Matrix.Norms.L2Operator
variable {k n : ℕ}

/-- Consecutive true search midpoints differ by half the adjacent CG steps.
Article: main_krylov, thm:Htransfer, compatible tensor increments. -/
theorem rfcReferenceSearchMidpoint_sub {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (Q : E →L[ℝ] E) (u : E) (l : ℕ) :
    rfcReferenceSearchMidpoint Q u (l+1)-rfcReferenceSearchMidpoint Q u l=
      (1/2:ℝ) • (referenceStep Q (Q u) l+referenceStep Q (Q u) (l+1)) := by
  have he : fcQuadraticReferencePoint Q u (l+1)=fcQuadraticReferencePoint Q u l+referenceStep Q (Q u) l :=
    ((sub_eq_iff_eq_add).mp (fcQuadraticReferencePoint_step Q u l)).trans (add_comm _ _)
  simp only [rfcReferenceSearchMidpoint,he]
  module

/-- The true correction midpoint has a half-last-step increment at leading order.
Article: main_krylov, thm:Htransfer. -/
theorem rfcReferenceCorrectionMidpoint_sub {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (Q : E →L[ℝ] E) (u : E) (l : ℕ) :
    fcQuadraticReferencePoint Q u (l+1)-rfcReferenceSearchMidpoint Q u l=
      (1/2:ℝ) • referenceStep Q (Q u) l := by
  have he : fcQuadraticReferencePoint Q u (l+1)=fcQuadraticReferencePoint Q u l+referenceStep Q (Q u) l :=
    ((sub_eq_iff_eq_add).mp (fcQuadraticReferencePoint_step Q u l)).trans (add_comm _ _)
  simp only [rfcReferenceSearchMidpoint,he]
  module

/-- Genuine canonical compatible tensor increments at half adjacent steps.
Article: main_krylov, thm:Htransfer, T[ξ_l]. -/
def rfcCompatibleIncrements (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (D : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (u : EuclideanSpace ℝ (Fin n)) (l : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  physicalCanonicalMatrix base hb (D ((1/2:ℝ) •
    (referenceStep (cgOperator base) (cgOperator base u) l+
      referenceStep (cgOperator base) (cgOperator base u) (l+1))))

/-- Genuine canonical final correction slice at half the last reference step.
Article: main_krylov, thm:Htransfer, T[ζ_(n−1)]. -/
def rfcCompatibleCorrection (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (D : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (u : EuclideanSpace ℝ (Fin n)) (l : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  physicalCanonicalMatrix base hb (D ((1/2:ℝ) • referenceStep (cgOperator base) (cgOperator base u) l))

/-- The literal true-function RFC tensor coefficient is exactly the printed
canonical staircase/fresh-defect product. Article: main_krylov, thm:Htransfer.
No common first-secant normalization or tensor response identity is assumed. -/
theorem rfcTensorPhysicalCoefficient_eq_canonical
    (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (D : EuclideanSpace ℝ (Fin (k+1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1)))
    (u : EuclideanSpace ℝ (Fin (k+1)))
    (hN : k+1≤referenceAtomCount base hb (cgOperator base u)) :
    cgOperator (metricRoot base)⁻¹ (rfcTensorPhysicalCoefficient base D u)=
      ‖canonicalCGStep base (cgOperator base u) k‖ •
      staircaseOperator base (cgOperator base u) (rfcCompatibleIncrements base hb D u)
        (rfcCompatibleCorrection base hb D u k) (k+1)
        (freshDefect base (cgOperator base u) (rfcCompatibleIncrements base hb D u) (k+1)) := by
  have hA l : rfcTensorSearch (cgOperator base) D u (l+1)-rfcTensorSearch (cgOperator base) D u l=
      D ((1/2:ℝ) • (referenceStep (cgOperator base) (cgOperator base u) l+
        referenceStep (cgOperator base) (cgOperator base u) (l+1))) := by
    simp only [rfcTensorSearch,add_sub_add_left_eq_sub,←map_sub,rfcReferenceSearchMidpoint_sub]
  have hB : rfcTensorCorrection (cgOperator base) D u k-rfcTensorSearch (cgOperator base) D u k=
      D ((1/2:ℝ) • referenceStep (cgOperator base) (cgOperator base u) k) := by
    simp only [rfcTensorCorrection,rfcTensorSearch,add_sub_add_left_eq_sub,←map_sub,rfcReferenceCorrectionMidpoint_sub]
  unfold rfcTensorPhysicalCoefficient
  rw [rfcPhysicalQuadratic_eq_canonical base hb _ hN]
  simp only [hA,hB]
  rfl

/-- The printed canonical cubic response of a compatible third derivative.
Article: main_krylov, thm:Htransfer, norm(last step) times L times fresh defect. -/
def rfcTensorCanonicalCoefficient
    (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (D : EuclideanSpace ℝ (Fin (k+1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1)))
    (u : EuclideanSpace ℝ (Fin (k+1))) : EuclideanSpace ℝ (Fin (k+1)) :=
  ‖canonicalCGStep base (cgOperator base u) k‖ •
    staircaseOperator base (cgOperator base u) (rfcCompatibleIncrements base hb D u)
      (rfcCompatibleCorrection base hb D u k) (k+1)
      (freshDefect base (cgOperator base u) (rfcCompatibleIncrements base hb D u) (k+1))

set_option maxHeartbeats 800000 in
/-- The true native RFC terminal gradient has the printed compatible tensor
staircase product in the actual minimizer metric, uniformly over compact
full-atom reference families. Article: main_krylov, thm:Htransfer. -/
theorem metricRFCPoint_spatial_leading_gradient
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
          (G (rfcFunctionPoint (metricCoordinates base hb) f G fullMemory r (ε • u) (k+1)))+
        ε^3 • rfcTensorCanonicalCoefficient base hb D u‖≤η*ε^3 := by
  have hpre : ∀ g∈K, ∀ i≤k, CG.gradient (cgOperator base) g i≠0 := by
    intro g hg i hi
    exact cg_nonstagnation_of_full_atoms base hb g (hcount g hg) i (by omega)
  let J := ‖(metricCoordinates base hb).symm.toContinuousLinearMap‖
  have hJ : 0≤J := norm_nonneg _
  intro η hη
  obtain ⟨ep,hep,hbound⟩ := nativeRFC_tensor_cubic_remainder base hb hk (metricCoordinates base hb)
    (metricCoordinates_inverse_symmetric base hb) f G H D hD hr hG₀ hH₀
    (coordinateDerivative_metric_zero base hb H hH₀) hLr hH hF hG K hK hpre R hR
    (η/(J+1)) (by positivity)
  refine ⟨ep,hep,?_⟩
  intro ε hε he u hu hKu
  have hp := hbound ε hε he u hu hKu
  have hc := rfcTensorPhysicalCoefficient_eq_canonical base hb D u (by rw [hcount _ hKu])
  have hn := (metricCoordinates base hb).symm.toContinuousLinearMap.le_opNorm
    (G (rfcFunctionPoint (metricCoordinates base hb) f G fullMemory r (ε • u) (k+1))+
      ε^3 • rfcTensorPhysicalCoefficient base D u)
  rw [map_add,map_smul] at hn
  change ‖cgOperator (metricRoot base)⁻¹
      (G (rfcFunctionPoint (metricCoordinates base hb) f G fullMemory r (ε • u) (k+1)))+
      ε^3 • cgOperator (metricRoot base)⁻¹ (rfcTensorPhysicalCoefficient base D u)‖≤_ at hn
  rw [hc] at hn
  change ‖_+ε^3 • rfcTensorCanonicalCoefficient base hb D u‖≤_ at hn
  have hcoef : J*(η/(J+1))≤η := by
    have hh : η/(J+1)*(J+1)=η := by field_simp
    nlinarith only [hh,div_nonneg hη.le (by positivity : 0≤J+1)]
  apply hn.trans
  change J*‖G (rfcFunctionPoint (metricCoordinates base hb) f G fullMemory r (ε • u) (k+1))+
    ε^3 • rfcTensorPhysicalCoefficient base D u‖≤η*ε^3
  calc
    _ ≤ J*(η/(J+1)*ε^3) := mul_le_mul_of_nonneg_left hp hJ
    _ = (J*(η/(J+1)))*ε^3 := by ring
    _ ≤ η*ε^3 := mul_le_mul_of_nonneg_right hcoef (pow_nonneg hε.le 3)

end
end krylov.Functions
