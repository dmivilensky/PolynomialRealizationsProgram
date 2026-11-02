import krylov.Functions.RFCFOwnCanonical

/-!
Article: main_krylov, prop:Fcycle(i), actual own-A₀ corrected tensor response.
Use: identify the genuine native value-corrected coefficient in the canonical
metric of its actual first secant and independently observed initial gradient.
Source: actual raw diagonal compression, genuine reference differences and
exact nonsingular full-coordinate cancellation.
-/
namespace krylov.Functions
noncomputable section
open Set Metric Matrix Finset krylov.Methods krylov.Reference krylov.Nonlinear krylov.Correction
  krylov.Secant krylov.Variation krylov.Envelope
open scoped InnerProductSpace NNReal BigOperators Matrix.Norms.L2Operator
variable {k : ℕ}

set_option maxHeartbeats 800000 in
/-- The actual own-first-secant canonical metric has exactly the printed
native RFC compatible tensor leading term, uniformly over the original
compact observed-reference family. All inverse-root bounds are derived.
Article: main_krylov, prop:Fcycle(i), own-A₀ spatial formula. -/
theorem metricRFCFPoint_own_spatial_leading_gradient
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
    (R : ℝ) (hR : 0<R)
    (Kown : Set ((EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1))) ×
      EuclideanSpace ℝ (Fin (k+1)))) (hKown : IsCompact Kown)
    (hquad : ∀ z∈Kown, z.1.toLinearMap.IsSymmetric ∧
      (∀ w, w≠0 → 0 < inner ℝ w (z.1 w)) ∧ ∀ i<k+1, CG.gradient z.1 z.2 i≠0) :
    ∀ η : ℝ, 0<η → ∃ ε₀ : ℝ, 0<ε₀ ∧ ∀ ε : ℝ, 0<ε → ε<ε₀ →
      ∀ u : EuclideanSpace ℝ (Fin (k+1)), ‖u‖≤R → cgOperator base u∈K →
      let A₀ := rfcFunctionSearchOperator T f G H fullMemory r (ε • u) 0
      let b := physicalOperatorMatrix A₀
      let g := ε⁻¹ • G (ε • u)
      (A₀,g)∈Kown → ∃ hbown : b.PosDef,
      ‖cgOperator (metricRoot b)⁻¹
          (G (rfcFPoint T f G r (ε • u) k))+
        ε^3 • rfcFOwnTensorCanonicalCoefficient b hbown D g‖≤η*ε^3 := by
  obtain ⟨M,hM,hmetric⟩ := own_inverseRoot_compact_bound Kown hKown
    (fun z hz=>⟨(hquad z hz).1,(hquad z hz).2.1⟩)
  intro η hη
  obtain ⟨ep,hep,hphysical⟩ := nativeRFCF_own_tensor_cubic_remainder base hb hk T hT f G H D hD
    hr hG₀ hH₀ hHc₀ hLr hH hF hG K hK hpre R hR (η/(M+1)) (by positivity)
  refine ⟨ep,hep,?_⟩
  intro ε hε he u hu hKu
  dsimp only
  let A₀ := rfcFunctionSearchOperator T f G H fullMemory r (ε • u) 0
  let b := physicalOperatorMatrix A₀
  let g := ε⁻¹ • G (ε • u)
  intro hown
  have hbown : b.PosDef := physicalOperatorMatrix_posDef A₀ (hquad _ hown).1 (hquad _ hown).2.1
  have hcount : referenceAtomCount b hbown g=k+1 := by
    apply referenceAtomCount_eq_of_full_nonstagnation
    rw [physicalOperatorMatrix_operator]
    exact (hquad _ hown).2.2
  have hc := rfcFOwnTensorPhysicalCoefficient_eq_canonical b hbown D g u (by rw [hcount])
  have hp := hphysical ε hε he u hu hKu
  have hn := (cgOperator (metricRoot b)⁻¹).le_opNorm
    (G (rfcFPoint T f G r (ε • u) k)+ε^3 • rfcFOwnTensorPhysicalCoefficient b D g u)
  rw [map_add,map_smul,hc] at hn
  have hroot : ‖cgOperator (metricRoot b)⁻¹‖≤M := hmetric (A₀,g) hown
  have hcoe : M*(η/(M+1))≤η := by
    have hh : η/(M+1)*(M+1)=η := by field_simp
    nlinarith only [hh,div_nonneg hη.le (by positivity : 0≤M+1)]
  refine ⟨hbown,hn.trans ?_⟩
  calc
    _ ≤ M*‖G (rfcFPoint T f G r (ε • u) k)+ε^3 • rfcFOwnTensorPhysicalCoefficient b D g u‖ :=
      mul_le_mul_of_nonneg_right hroot (norm_nonneg _)
    _ ≤ M*(η/(M+1)*ε^3) := mul_le_mul_of_nonneg_left hp hM
    _ = (M*(η/(M+1)))*ε^3 := by ring
    _ ≤ η*ε^3 := mul_le_mul_of_nonneg_right hcoe (pow_nonneg hε.le 3)

set_option maxHeartbeats 800000 in
/-- Genuine Lip-D3 gives the printed own-first-secant canonical RFC-F tensor
response with a compact-uniform fourth-order actual gradient remainder.
Article: main_krylov, prop:Fcycle(i). -/
theorem metricRFCFPoint_own_spatial_quartic_remainder
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
    (R : ℝ) (hR : 0<R)    (Kown : Set ((EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1))) ×
      EuclideanSpace ℝ (Fin (k+1)))) (hKown : IsCompact Kown)
    (hquad : ∀ z∈Kown, z.1.toLinearMap.IsSymmetric ∧
      (∀ w, w≠0 → 0 < inner ℝ w (z.1 w)) ∧ ∀ i<k+1, CG.gradient z.1 z.2 i≠0) :
    ∃ ε₀ C : ℝ, 0<ε₀ ∧ 0<C ∧ ∀ ε : ℝ, 0<ε → ε<ε₀ →
      ∀ u : EuclideanSpace ℝ (Fin (k+1)), ‖u‖≤R → cgOperator base u∈K →
      let A₀ := rfcFunctionSearchOperator T f G H fullMemory r (ε • u) 0
      let b := physicalOperatorMatrix A₀
      let g := ε⁻¹ • G (ε • u)
      (A₀,g)∈Kown → ∃ hbown : b.PosDef,
      ‖cgOperator (metricRoot b)⁻¹
          (G (rfcFPoint T f G r (ε • u) k))+
        ε^3 • rfcFOwnTensorCanonicalCoefficient b hbown (D 0) g‖≤C*ε^4 := by
  obtain ⟨M,hM,hmetric⟩ := own_inverseRoot_compact_bound Kown hKown
    (fun z hz=>⟨(hquad z hz).1,(hquad z hz).2.1⟩)
  obtain ⟨ep,Cp,hep,hCp,hphysical⟩ := nativeRFCF_own_tensor_quartic_remainder base hb hk T hT f G H D
    hr hG₀ hH₀ hHc₀ hLr hH hD hDlip hF hG K hK hpre R hR
  refine ⟨ep,M*Cp+1,hep,by positivity,?_⟩
  intro ε hε he u hu hKu
  dsimp only
  let A₀ := rfcFunctionSearchOperator T f G H fullMemory r (ε • u) 0
  let b := physicalOperatorMatrix A₀
  let g := ε⁻¹ • G (ε • u)
  intro hown
  have hbown : b.PosDef := physicalOperatorMatrix_posDef A₀ (hquad _ hown).1 (hquad _ hown).2.1
  have hcount : referenceAtomCount b hbown g=k+1 := by
    apply referenceAtomCount_eq_of_full_nonstagnation
    rw [physicalOperatorMatrix_operator]
    exact (hquad _ hown).2.2
  have hc := rfcFOwnTensorPhysicalCoefficient_eq_canonical b hbown (D 0) g u (by rw [hcount])
  have hp := hphysical ε hε he u hu hKu
  have hn := (cgOperator (metricRoot b)⁻¹).le_opNorm
    (G (rfcFPoint T f G r (ε • u) k)+ε^3 • rfcFOwnTensorPhysicalCoefficient b (D 0) g u)
  rw [map_add,map_smul,hc] at hn
  have hroot : ‖cgOperator (metricRoot b)⁻¹‖≤M := hmetric (A₀,g) hown
  refine ⟨hbown,hn.trans ?_⟩
  calc
    _ ≤ M*‖G (rfcFPoint T f G r (ε • u) k)+ε^3 • rfcFOwnTensorPhysicalCoefficient b (D 0) g u‖ :=
      mul_le_mul_of_nonneg_right hroot (norm_nonneg _)
    _ ≤ M*(Cp*ε^4) := mul_le_mul_of_nonneg_left hp hM
    _ ≤ (M*Cp+1)*ε^4 := by nlinarith only [pow_nonneg hε.le 4]

end
end krylov.Functions
