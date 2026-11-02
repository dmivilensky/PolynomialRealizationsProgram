import krylov.Functions.NativeRFCTensorComparison

/-!
Article: main_krylov, thm:Htransfer, native ordinary RFC tensor leading term.
Use: apply the actual third derivative at the minimizer to the true nonlinear
RFC executor, uniformly over compact nondegenerate quadratic references.
Source: genuine query first jets, the exact physical quadratic response and
its proved compact cubic remainder. No output expansion is assumed.
-/
namespace krylov.Functions
noncomputable section
open Set Metric Matrix krylov.Methods krylov.Reference krylov.Nonlinear
open scoped InnerProductSpace NNReal Matrix.Norms.L2Operator
variable {k : ℕ}

/-- Substitution into an actual cubic-scale residual retains its true gain.
Article: main_krylov, thm:Htransfer, triangle inequality bookkeeping. -/
theorem cubic_response_substitution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g a b : E) (ε A B J : ℝ) (hε : 0≤ε)
    (ha : ‖g+ε • a‖≤A*ε^4) (hb : ‖a-ε^2 • b‖≤B*ε*J) :
    ‖g+ε^3 • b‖≤A*ε^4+B*ε^2*J := by
  have he : g+ε^3 • b=(g+ε • a)+ε • (ε^2 • b-a) := by module
  rw [he]
  have hn : ‖ε • (ε^2 • b-a)‖≤B*ε^2*J := by
    rw [norm_smul,Real.norm_of_nonneg hε,norm_sub_rev]
    exact (mul_le_mul_of_nonneg_left hb hε).trans_eq (by ring)
  exact (norm_add_le _ _).trans (add_le_add ha hn)

set_option maxHeartbeats 800000 in
/-- The genuine ordinary RFC cycle has its original-third-derivative cubic
leading term, with a uniform little-o remainder. The executor uses actual
objective minima and actual gradient correction queries.
Article: main_krylov, thm:Htransfer, ordinary RFC cubic transfer. -/
theorem nativeRFC_tensor_cubic_remainder
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
      ‖G (rfcFunctionPoint T f G fullMemory r (ε • u) (k+1))+
        ε^3 • rfcTensorPhysicalCoefficient base D u‖≤η*ε^3 := by
  obtain ⟨ep,Cp,hep,hCp,hphysical⟩ := nativeRFC_physical_quadratic_remainder base hb hk T hT f G H
    hr hG₀ hH₀ hHc₀ hLr hH hF hG K hK hpre R hR
  obtain ⟨et,Ct,het,hCt,hcomparison⟩ := nativeRFC_tensor_comparison base hb T hT f G H D hD
    hr hG₀ hH₀ hHc₀ hLr hH hF hG K hK hpre R hR
  obtain ⟨hQ,hpos⟩ := cgOperator_positive base hb
  intro η hη
  let ζ := η/(2*(Ct+1))
  have hζ : 0<ζ := by dsimp only [ζ]; positivity
  obtain ⟨ej,hej,hjets⟩ := nativeRFC_reference_operator_jets T hT f G H (cgOperator base) D hD
    hr hG₀ hH₀ hHc₀ hLr hH hF hG hQ hpos (k+1) K hK
    (fun g hg i hi=>hpre g hg i (by omega)) R hR ζ hζ
  let ε₀ := min ep (min et (min ej (η/(2*(Cp+1)))))
  have hε₀ : 0<ε₀ := by dsimp only [ε₀]; positivity
  refine ⟨ε₀,hε₀,?_⟩
  intro ε hε he u hu hKu
  have heep : ε<ep := he.trans_le (min_le_left _ _)
  have heet : ε<et := he.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have heej : ε<ej := he.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hp := hphysical ε hε heep u hu hKu
  have hc := hcomparison ε hε heet u hu hKu (ζ*ε) (by positivity)
    (hjets ε hε heej u hu hKu)
  have hb := cubic_response_substitution _ _ _ ε Cp Ct (ζ*ε) hε.le hp hc
  have hCpε : Cp*ε≤η/2 := by
    have hh := (lt_div_iff₀ (by positivity : 0<2*(Cp+1))).mp
      (he.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
    nlinarith only [hh,hε]
  have hCtζ : Ct*ζ≤η/2 := by
    have hh : 2*(Ct+1)*ζ=η := by dsimp only [ζ]; field_simp
    nlinarith only [hh,hζ]
  have hp4 := mul_le_mul_of_nonneg_right hCpε (pow_nonneg hε.le 3)
  have hc3 := mul_le_mul_of_nonneg_right hCtζ (pow_nonneg hε.le 3)
  nlinarith only [hb,hp4,hc3]

set_option maxHeartbeats 800000 in
/-- A genuine Lipschitz third derivative gives a uniform fourth-order remainder
for the actual ordinary RFC terminal gradient, with the same exact tensor
coefficient. Both derivative regularity and all algorithmic queries concern
the original scalar objective. Article: main_krylov, thm:Htransfer. -/
theorem nativeRFC_tensor_quartic_remainder
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
      ‖G (rfcFunctionPoint T f G fullMemory r (ε • u) (k+1))+
        ε^3 • rfcTensorPhysicalCoefficient base (D 0) u‖≤C*ε^4 := by
  have hD₀ : HasFDerivAt H (D 0) 0 := hD 0 (by simpa only [map_zero,norm_zero] using hr.le)
  obtain ⟨ep,Cp,hep,hCp,hphysical⟩ := nativeRFC_physical_quadratic_remainder base hb hk T hT f G H
    hr hG₀ hH₀ hHc₀ hLr hH hF hG K hK hpre R hR
  obtain ⟨et,Ct,het,hCt,hcomparison⟩ := nativeRFC_tensor_comparison base hb T hT f G H (D 0) hD₀
    hr hG₀ hH₀ hHc₀ hLr hH hF hG K hK hpre R hR
  obtain ⟨hQ,hpos⟩ := cgOperator_positive base hb
  obtain ⟨ej,Cj,hej,hCj,hjets⟩ := nativeRFC_reference_operator_jets_quadratic T hT f G H (cgOperator base) D
    hr hG₀ hH₀ hHc₀ hLr hH hD hDlip hF hG hQ hpos (k+1) K hK
    (fun g hg i hi=>hpre g hg i (by omega)) R hR
  let ε₀ := min ep (min et ej)
  have hε₀ : 0<ε₀ := by dsimp only [ε₀]; positivity
  refine ⟨ε₀,Cp+Ct*Cj,hε₀,by positivity,?_⟩
  intro ε hε he u hu hKu
  have hp := hphysical ε hε (he.trans_le (min_le_left _ _)) u hu hKu
  have hc := hcomparison ε hε (he.trans_le ((min_le_right _ _).trans (min_le_left _ _))) u hu hKu
    (Cj*ε^2) (by positivity)
    (hjets ε hε (he.trans_le ((min_le_right _ _).trans (min_le_right _ _))) u hu hKu)
  exact (cubic_response_substitution _ _ _ ε Cp Ct (Cj*ε^2) hε.le hp hc).trans_eq (by ring)

end
end krylov.Functions
