import krylov.Functions.NativeRFCOwnSource
import krylov.Functions.RFCFOwnTensor

/-!
Article: main_krylov, prop:Fcycle(i), complete true own-reference RFC tensor transfer.
Use: retain the actual first search secant, the original observed initial
gradient and all original CG midpoint tensor slices in the genuine nonlinear
RFC output. Source: actual scalar-function transfer and proved compact joint
analytic dependence of its literal tensor coefficient.
-/
namespace krylov.Functions
noncomputable section
open Set Metric Matrix krylov.Methods krylov.Reference krylov.Nonlinear
open scoped InnerProductSpace NNReal Matrix.Norms.L2Operator
variable {k : ℕ}

set_option maxHeartbeats 800000 in
/-- Value-corrected RFC-F has the true original-A₀ compatible-tensor cubic leading
term, uniformly on compact nondegenerate reference families.
The initial gradient and first secant are the actual observations, not
prescribed reference data. Article: main_krylov, prop:Fcycle(i). -/
theorem nativeRFCF_own_tensor_cubic_remainder
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
    (hF : ∀ z, ‖T z‖≤r → HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z, ‖T z‖≤r → HasFDerivAt G (H z) z)
    (K : Set (EuclideanSpace ℝ (Fin (k+1)))) (hK : IsCompact K)
    (hpre : ∀ g∈K, ∀ i≤k, CG.gradient (cgOperator base) g i≠0)
    (R : ℝ) (hR : 0<R) :
    ∀ η : ℝ, 0<η → ∃ ε₀ : ℝ, 0<ε₀ ∧ ∀ ε : ℝ, 0<ε → ε<ε₀ →
      ∀ u : EuclideanSpace ℝ (Fin (k+1)), ‖u‖≤R → cgOperator base u∈K →
      let A₀ := rfcFunctionSearchOperator T f G H fullMemory r (ε • u) 0
      let b := physicalOperatorMatrix A₀
      let g := ε⁻¹ • G (ε • u)
      ‖G (rfcFPoint T f G r (ε • u) k)+
        ε^3 • rfcFOwnTensorPhysicalCoefficient b D g u‖≤η*ε^3 := by
  obtain ⟨es,Cs,hes,hCs,hsource⟩ := nativeRFC_own_reference_drift base hb T hT f G H hr hG₀ hH₀ hHc₀
    hLr hH hF hG K hK hpre R hR
  obtain ⟨δ,Ca,hδ,hCa,hchange⟩ := compact_rfcFOwnTensorPhysicalCoefficient_reference_change base hb D K hK hpre R
  intro η hη
  obtain ⟨ef,hef,hfixed⟩ := nativeRFCF_tensor_cubic_remainder base hb hk T hT f G H D hD
    hr hG₀ hH₀ hHc₀ hLr hH hF hG K hK hpre R hR (η/2) (by positivity)
  let ε₀ := min es (min ef (min (δ/(Cs+1)) (η/(2*(Ca*Cs+1)))))
  have hε₀ : 0<ε₀ := by dsimp only [ε₀]; positivity
  refine ⟨ε₀,hε₀,?_⟩
  intro ε hε he u hu hKu
  let b := physicalOperatorMatrix (rfcFunctionSearchOperator T f G H fullMemory r (ε • u) 0)
  let g := ε⁻¹ • G (ε • u)
  have hs : ‖(b-base,g-cgOperator base u)‖≤Cs*ε :=
    hsource ε hε (he.trans_le (min_le_left _ _)) u hu hKu
  have hsmall : ‖(b-base,g-cgOperator base u)‖≤δ := by
    have hh := (lt_div_iff₀ (by positivity : 0<Cs+1)).mp
      (he.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
    exact hs.trans (by nlinarith only [hh,hε])
  have hc := hchange (cgOperator base u) hKu u hu (b-base) (g-cgOperator base u) hsmall
  have hb₀ : base+(b-base)=b := by abel
  have hg₀ : cgOperator base u+(g-cgOperator base u)=g := by abel
  rw [hb₀,hg₀,rfcFOwnTensorPhysicalCoefficient_quadratic] at hc
  have hcb := hc.trans (mul_le_mul_of_nonneg_left hs hCa.le)
  have hfixed' := hfixed ε hε (he.trans_le ((min_le_right _ _).trans (min_le_left _ _))) u hu hKu
  have heq : G (rfcFPoint T f G r (ε • u) k)+ε^3 • rfcFOwnTensorPhysicalCoefficient b D g u=
      (G (rfcFPoint T f G r (ε • u) k)+ε^3 • rfcFTensorPhysicalCoefficient base D u)+
        ε^3 • (rfcFOwnTensorPhysicalCoefficient b D g u-rfcFTensorPhysicalCoefficient base D u) := by module
  change ‖G (rfcFPoint T f G r (ε • u) k)+ε^3 • rfcFOwnTensorPhysicalCoefficient b D g u‖≤_
  rw [heq]
  have hn : ‖ε^3 • (rfcFOwnTensorPhysicalCoefficient b D g u-rfcFTensorPhysicalCoefficient base D u)‖≤
      ε^3*(Ca*(Cs*ε)) := by
    rw [norm_smul,Real.norm_of_nonneg (pow_nonneg hε.le 3)]
    exact mul_le_mul_of_nonneg_left hcb (pow_nonneg hε.le 3)
  have hb := (norm_add_le _ _).trans (add_le_add hfixed' hn)
  have hcoeff : Ca*Cs*ε≤η/2 := by
    have hh := (lt_div_iff₀ (by positivity : 0<2*(Ca*Cs+1))).mp
      (he.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
    nlinarith only [hh,hε]
  have hh := mul_le_mul_of_nonneg_right hcoeff (pow_nonneg hε.le 3)
  nlinarith only [hb,hh]

set_option maxHeartbeats 800000 in
/-- Genuine Lip-D3 yields the same original-A₀ tensor response with a uniform
fourth-order native RFC gradient remainder. Article: main_krylov, prop:Fcycle(i). -/
theorem nativeRFCF_own_tensor_quartic_remainder
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
    (hF : ∀ z, ‖T z‖≤r → HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z, ‖T z‖≤r → HasFDerivAt G (H z) z)
    (K : Set (EuclideanSpace ℝ (Fin (k+1)))) (hK : IsCompact K)
    (hpre : ∀ g∈K, ∀ i≤k, CG.gradient (cgOperator base) g i≠0)
    (R : ℝ) (hR : 0<R) :
    ∃ ε₀ C : ℝ, 0<ε₀ ∧ 0<C ∧ ∀ ε : ℝ, 0<ε → ε<ε₀ →
      ∀ u : EuclideanSpace ℝ (Fin (k+1)), ‖u‖≤R → cgOperator base u∈K →
      let A₀ := rfcFunctionSearchOperator T f G H fullMemory r (ε • u) 0
      let b := physicalOperatorMatrix A₀
      let g := ε⁻¹ • G (ε • u)
      ‖G (rfcFPoint T f G r (ε • u) k)+
        ε^3 • rfcFOwnTensorPhysicalCoefficient b (D 0) g u‖≤C*ε^4 := by
  obtain ⟨es,Cs,hes,hCs,hsource⟩ := nativeRFC_own_reference_drift base hb T hT f G H hr hG₀ hH₀ hHc₀
    hLr hH hF hG K hK hpre R hR
  obtain ⟨δ,Ca,hδ,hCa,hchange⟩ := compact_rfcFOwnTensorPhysicalCoefficient_reference_change base hb (D 0) K hK hpre R
  obtain ⟨ef,Cf,hef,hCf,hfixed⟩ := nativeRFCF_tensor_quartic_remainder base hb hk T hT f G H D
    hr hG₀ hH₀ hHc₀ hLr hH hD hDlip hF hG K hK hpre R hR
  let ε₀ := min es (min ef (δ/(Cs+1)))
  have hε₀ : 0<ε₀ := by dsimp only [ε₀]; positivity
  refine ⟨ε₀,Cf+Ca*Cs,hε₀,by positivity,?_⟩
  intro ε hε he u hu hKu
  let b := physicalOperatorMatrix (rfcFunctionSearchOperator T f G H fullMemory r (ε • u) 0)
  let g := ε⁻¹ • G (ε • u)
  have hs : ‖(b-base,g-cgOperator base u)‖≤Cs*ε :=
    hsource ε hε (he.trans_le (min_le_left _ _)) u hu hKu
  have hsmall : ‖(b-base,g-cgOperator base u)‖≤δ := by
    have hh := (lt_div_iff₀ (by positivity : 0<Cs+1)).mp
      (he.trans_le ((min_le_right _ _).trans (min_le_right _ _)))
    exact hs.trans (by nlinarith only [hh,hε])
  have hc := hchange (cgOperator base u) hKu u hu (b-base) (g-cgOperator base u) hsmall
  have hb₀ : base+(b-base)=b := by abel
  have hg₀ : cgOperator base u+(g-cgOperator base u)=g := by abel
  rw [hb₀,hg₀,rfcFOwnTensorPhysicalCoefficient_quadratic] at hc
  have hcb := hc.trans (mul_le_mul_of_nonneg_left hs hCa.le)
  have hfixed' := hfixed ε hε (he.trans_le ((min_le_right _ _).trans (min_le_left _ _))) u hu hKu
  have heq : G (rfcFPoint T f G r (ε • u) k)+ε^3 • rfcFOwnTensorPhysicalCoefficient b (D 0) g u=
      (G (rfcFPoint T f G r (ε • u) k)+ε^3 • rfcFTensorPhysicalCoefficient base (D 0) u)+
        ε^3 • (rfcFOwnTensorPhysicalCoefficient b (D 0) g u-rfcFTensorPhysicalCoefficient base (D 0) u) := by module
  change ‖G (rfcFPoint T f G r (ε • u) k)+ε^3 • rfcFOwnTensorPhysicalCoefficient b (D 0) g u‖≤_
  rw [heq]
  apply (norm_add_le _ _).trans
  rw [norm_smul,Real.norm_of_nonneg (pow_nonneg hε.le 3)]
  calc
    _ ≤ Cf*ε^4+ε^3*(Ca*(Cs*ε)) := add_le_add hfixed' (mul_le_mul_of_nonneg_left hcb (pow_nonneg hε.le 3))
    _ = (Cf+Ca*Cs)*ε^4 := by ring

end
end krylov.Functions
