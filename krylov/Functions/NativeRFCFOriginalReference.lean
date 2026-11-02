import krylov.Functions.NativeRFCFOwnSpatialResponse
import krylov.Functions.OwnReferenceTube
import krylov.Functions.NativeRFCFirstSource

/-!
Article: main_krylov, s7:N and prop:Fcycle(i), original observed-reference RFC-F.
Use: state the true native tensor transfer using only the original compact
observed first-secant references. The auxiliary frozen-Hessian full-reference
set is derived from genuine first-query source bounds and compact CG openness.
No independent frozen-reference nondegeneracy premise remains.
-/
namespace krylov.Functions
noncomputable section
open Set Metric Matrix krylov.Methods krylov.Reference krylov.Nonlinear krylov.Secant
open scoped InnerProductSpace NNReal Matrix.Norms.L2Operator
variable {k : ℕ}

set_option maxHeartbeats 800000 in
/-- Genuine original-observed-reference RFC tensor transfer, with the full
uniform cubic little-o remainder.
Only the original compact nondegeneracy of the actual first-secant/gradient
pairs is assumed; every auxiliary frozen reference is derived.
Article: main_krylov, prop:Fcycle(i). -/
theorem metricRFCFPoint_original_spatial_leading_gradient
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
    (R : ℝ) (hR : 0<R)
    (K : Set ((EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1))) ×
      EuclideanSpace ℝ (Fin (k+1)))) (hK : IsCompact K)
    (hquad : ∀ z∈K, z.1.toLinearMap.IsSymmetric ∧
      (∀ w, w≠0 → 0 < inner ℝ w (z.1 w)) ∧ ∀ i<k+1, CG.gradient z.1 z.2 i≠0) :
    ∀ η : ℝ, 0<η → ∃ ε₀ : ℝ, 0<ε₀ ∧ ∀ ε : ℝ, 0<ε → ε<ε₀ →
      ∀ u : EuclideanSpace ℝ (Fin (k+1)), ‖u‖≤R →
      let A₀ := rfcFunctionSearchOperator T f G H fullMemory r (ε • u) 0
      let b := physicalOperatorMatrix A₀
      let g := ε⁻¹ • G (ε • u)
      (A₀,g)∈K → ∃ hbown : b.PosDef,
      ‖cgOperator (metricRoot b)⁻¹
          (G (rfcFPoint T f G r (ε • u) k))+
        ε^3 • rfcFOwnTensorCanonicalCoefficient b hbown D g‖≤η*ε^3 := by
  obtain ⟨δ,hδ,F,hF,hpre,hcover⟩ := compact_own_reference_frozen_tube (cgOperator base) (k+1) K hK hquad
  obtain ⟨es,Cs,hes,hCs,hsource⟩ := nativeRFC_first_reference_drift T hT f G H (cgOperator base)
    hr hG₀ hH₀ hHc₀ hLr hH hF₀ hG R hR
  intro η hη
  obtain ⟨ef,hef,htransfer⟩ := metricRFCFPoint_own_spatial_leading_gradient base hb hk T hT f G H D hD
    hr hG₀ hH₀ hHc₀ hLr hH hF₀ hG F hF (fun g hg i hi=>hpre g hg i (by omega)) R hR K hK hquad η hη
  let ε₀ := min es (min ef (δ/(Cs+1)))
  have hε₀ : 0<ε₀ := by dsimp only [ε₀]; positivity
  refine ⟨ε₀,hε₀,?_⟩
  intro ε hε he u hu
  dsimp only
  let A₀ := rfcFunctionSearchOperator T f G H fullMemory r (ε • u) 0
  let g := ε⁻¹ • G (ε • u)
  intro hown
  have hs := hsource ε hε (he.trans_le (min_le_left _ _)) u hu
  have hsmall : ‖(A₀-cgOperator base,g-cgOperator base u)‖≤δ := by
    have hh := (lt_div_iff₀ (by positivity : 0<Cs+1)).mp
      (he.trans_le ((min_le_right _ _).trans (min_le_right _ _)))
    exact hs.trans (by nlinarith only [hh,hε])
  have hfixed := hcover A₀ g (cgOperator base u) hown hsmall
  exact htransfer ε hε (he.trans_le ((min_le_right _ _).trans (min_le_left _ _))) u hu hfixed hown

set_option maxHeartbeats 800000 in
/-- Genuine original-observed-reference RFC tensor transfer, with the full
uniform fourth-order remainder for a genuine Lipschitz third derivative.
Only the original compact nondegeneracy of the actual first-secant/gradient
pairs is assumed; every auxiliary frozen reference is derived.
Article: main_krylov, prop:Fcycle(i). -/
theorem metricRFCFPoint_original_spatial_quartic_remainder
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
    (R : ℝ) (hR : 0<R)    (K : Set ((EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1))) ×
      EuclideanSpace ℝ (Fin (k+1)))) (hK : IsCompact K)
    (hquad : ∀ z∈K, z.1.toLinearMap.IsSymmetric ∧
      (∀ w, w≠0 → 0 < inner ℝ w (z.1 w)) ∧ ∀ i<k+1, CG.gradient z.1 z.2 i≠0) :
    ∃ ε₀ C : ℝ, 0<ε₀ ∧ 0<C ∧ ∀ ε : ℝ, 0<ε → ε<ε₀ →
      ∀ u : EuclideanSpace ℝ (Fin (k+1)), ‖u‖≤R →
      let A₀ := rfcFunctionSearchOperator T f G H fullMemory r (ε • u) 0
      let b := physicalOperatorMatrix A₀
      let g := ε⁻¹ • G (ε • u)
      (A₀,g)∈K → ∃ hbown : b.PosDef,
      ‖cgOperator (metricRoot b)⁻¹
          (G (rfcFPoint T f G r (ε • u) k))+
        ε^3 • rfcFOwnTensorCanonicalCoefficient b hbown (D 0) g‖≤C*ε^4 := by
  obtain ⟨δ,hδ,F,hF,hpre,hcover⟩ := compact_own_reference_frozen_tube (cgOperator base) (k+1) K hK hquad
  obtain ⟨es,Cs,hes,hCs,hsource⟩ := nativeRFC_first_reference_drift T hT f G H (cgOperator base)
    hr hG₀ hH₀ hHc₀ hLr hH hF₀ hG R hR
  obtain ⟨ef,Cf,hef,hCf,htransfer⟩ := metricRFCFPoint_own_spatial_quartic_remainder base hb hk T hT f G H D
    hr hG₀ hH₀ hHc₀ hLr hH hD hDlip hF₀ hG F hF (fun g hg i hi=>hpre g hg i (by omega)) R hR K hK hquad
  let ε₀ := min es (min ef (δ/(Cs+1)))
  have hε₀ : 0<ε₀ := by dsimp only [ε₀]; positivity
  refine ⟨ε₀,Cf,hε₀,hCf,?_⟩
  intro ε hε he u hu
  dsimp only
  let A₀ := rfcFunctionSearchOperator T f G H fullMemory r (ε • u) 0
  let g := ε⁻¹ • G (ε • u)
  intro hown
  have hs := hsource ε hε (he.trans_le (min_le_left _ _)) u hu
  have hsmall : ‖(A₀-cgOperator base,g-cgOperator base u)‖≤δ := by
    have hh := (lt_div_iff₀ (by positivity : 0<Cs+1)).mp
      (he.trans_le ((min_le_right _ _).trans (min_le_right _ _)))
    exact hs.trans (by nlinarith only [hh,hε])
  have hfixed := hcover A₀ g (cgOperator base u) hown hsmall
  exact htransfer ε hε (he.trans_le ((min_le_right _ _).trans (min_le_left _ _))) u hu hfixed hown

end
end krylov.Functions
