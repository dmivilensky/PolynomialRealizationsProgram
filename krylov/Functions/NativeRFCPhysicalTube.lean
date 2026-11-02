import krylov.Functions.NativeRFCPhysicalInputs

/-!
Article: main_krylov, lem:cycle-transfer and prop:Fcycle, complete actual
native RFC inputs in a genuine compact physical source tube.
Use: recover all true segment operators and the complete unchanged native
prefix in one independent finite symmetric chart, with a common source bound.
Source: the proved original native bootstrap, true scalar Schwarz symmetry,
actual matrix/operator isometry and genuine quadratic gradient Taylor bound.
-/
namespace krylov.Functions
noncomputable section
open Set Metric Matrix krylov.Methods krylov.Reference krylov.Nonlinear krylov.Correction
open scoped InnerProductSpace NNReal Matrix.Norms.L2Operator
variable {k : ℕ}

set_option maxHeartbeats 800000 in
/-- Every genuine compact native ordinary-RFC family enters any prescribed
positive physical source tube, retaining all true observations and actual query bounds.
Article: main_krylov, prop:Fcycle and lem:cycle-transfer.
No source chart, trajectory bound, operator symmetry or oracle identity is
assumed. The actual physical operators and whole observed histories are derived. -/
theorem nativeRFC_physical_source_tube
    (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (T : EuclideanSpace ℝ (Fin (k+1)) ≃L[ℝ] EuclideanSpace ℝ (Fin (k+1)))
    (hT : T.symm.toContinuousLinearMap.IsSymmetric)
    (f : EuclideanSpace ℝ (Fin (k+1)) → ℝ)
    (G : EuclideanSpace ℝ (Fin (k+1)) → EuclideanSpace ℝ (Fin (k+1)))
    (H : EuclideanSpace ℝ (Fin (k+1)) → EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1)))
    {r : ℝ} (hr : 0<r) (hG₀ : G 0=0) (hH₀ : H 0=cgOperator base)
    (hHc₀ : coordinateDerivative T H 0=ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin (k+1))))
    {L : ℝ≥0} (hLr : (L : ℝ)*r≤1/2)
    (hH : LipschitzOnWith L (coordinateDerivative T H) (closedBall 0 r))
    (hF : ∀ z, ‖T z‖≤r → HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z, ‖T z‖≤r → HasFDerivAt G (H z) z)
    (K : Set (EuclideanSpace ℝ (Fin (k+1)))) (hK : IsCompact K)
    (hpre : ∀ g∈K, ∀ i≤k, CG.gradient (cgOperator base) g i≠0)
    (R δ : ℝ) (hR : 0<R) (hδ : 0<δ) :
    ∃ ε₀ M D C S : ℝ, 0<ε₀ ∧ 0<M ∧ 0<D ∧ 0<C ∧ 0<S ∧
      ∀ ε : ℝ, 0<ε → ε<ε₀ → ∀ u : EuclideanSpace ℝ (Fin (k+1)), ‖u‖≤R → cgOperator base u∈K →
      NativeRFCPrefixBounds T f G H (cgOperator base) r u ε M D C (k+1) ∧
      ∃ Θ : RFCPhysicalData k,
        (∀ j≤k, rfcPhysicalSearch base Θ j=rfcFunctionSearchOperator T f G H fullMemory r (ε • u) j) ∧
        (∀ j≤k, rfcPhysicalCorrection base Θ j=rfcFunctionCorrectionOperator T f G H fullMemory r (ε • u) j) ∧
        (∀ j≤k+1,rfcFunctionRun T f G fullMemory r (ε • u) j=
          methodRun (rfcMethod fullMemory 1) (rfcPhysicalSearch base Θ) (rfcPhysicalCorrection base Θ) (G (ε • u)) j) ∧
        ‖(ε⁻¹ • G (ε • u)-cgOperator base u,Θ)‖≤S*ε ∧
        ‖(ε⁻¹ • G (ε • u)-cgOperator base u,Θ)‖≤δ ∧
        (∀ j≤k+1,‖T (rfcFunctionPoint T f G fullMemory r (ε • u) j)‖<r/2) := by
  let Q := cgOperator base
  obtain ⟨hQ,hpos⟩ := cgOperator_positive base hb
  obtain ⟨ep,M,D,C,hep,hM,hD,hC,hprefix⟩ := nativeRFC_compact_prefix T hT f G H Q hr hG₀ hH₀ hHc₀
    hLr hH hF hG hQ hpos (k+1) K hK (fun g hg i hi=>hpre g hg i (by omega)) R hR
  let P : ℝ := (((‖T.toContinuousLinearMap‖₊^3*L : ℝ≥0) : ℝ))
  let Dg := P/2*R^2
  let S := Dg+D+1
  have hP : 0≤P := NNReal.coe_nonneg _
  have hDg : 0≤Dg := by dsimp only [Dg]; positivity
  have hS : 0<S := by dsimp only [S]; positivity
  let ε₀ := min ep (min (r/(2*(‖T.toContinuousLinearMap‖*M+1))) (δ/(S+1)))
  have hε₀ : 0<ε₀ := by dsimp only [ε₀]; positivity
  refine ⟨ε₀,M,D,C,S,hε₀,hM,hD,hC,hS,?_⟩
  intro ε hε he u hu hKu
  have hp := hprefix ε hε (he.trans_le (min_le_left _ _)) u hu hKu
  have hscale : ‖T.toContinuousLinearMap‖*M*ε<r/2 := by
    have hh := (lt_div_iff₀ (by positivity : 0<2*(‖T.toContinuousLinearMap‖*M+1))).mp
      (he.trans_le ((min_le_right _ _).trans (min_le_left _ _)))
    nlinarith only [hh,hε]
  have hsym := hp.operator_symmetric T f G H Q r u ε M D C (k+1) (by linarith) hH hF hG
  let A := rfcFunctionSearchOperator T f G H fullMemory r (ε • u)
  let B := rfcFunctionCorrectionOperator T f G H fullMemory r (ε • u)
  have hA j (hj : j<k+1) : (A j).toLinearMap.IsSymmetric := (hsym j hj).1
  have hB j (hj : j<k+1) : (B j).toLinearMap.IsSymmetric := (hsym j hj).2
  let Θ := rfcPhysicalDataOfOperators base hQ A B hA hB
  have hΘ : ‖Θ‖≤D*ε := rfcPhysicalDataOfOperators_norm base hQ A B hA hB (D*ε) (by positivity)
    (fun j hj=>(hp.2 j hj).1) (fun j hj=>(hp.2 j hj).2.1)
  have hpoint j (hj : j≤k+1) : ‖T (rfcFunctionPoint T f G fullMemory r (ε • u) j)‖<r/2 :=
    ((T.toContinuousLinearMap.le_opNorm _).trans
      (mul_le_mul_of_nonneg_left (hp.1 j hj).1 (norm_nonneg _))).trans_lt (by simpa only [mul_assoc] using hscale)
  have hx₀ : ‖T (ε • u)‖≤r := by
    have h := hpoint 0 (by omega)
    simp only [rfcFunctionPoint,rfcFunctionRun,History.displacement,List.map_nil,List.sum_nil,add_zero] at h
    linarith only [h,hr]
  let v := ε⁻¹ • G (ε • u)-Q u
  have hv : ‖v‖≤Dg*ε := by
    have hh := metric_gradient_quadratic_error T G H Q hr.le hG₀ hH₀ hH hG (ε • u) hx₀
    have heq : v=ε⁻¹ • (G (ε • u)-Q (ε • u)) := by
      dsimp only [v]
      rw [smul_sub,map_smul,smul_smul,inv_mul_cancel₀ hε.ne',one_smul]
    rw [heq,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hε.le)]
    have hs : ‖u‖^2≤R^2 := (sq_le_sq₀ (norm_nonneg _) hR.le).mpr hu
    rw [norm_smul,Real.norm_of_nonneg hε.le] at hh
    calc
      _ ≤ ε⁻¹*(P/2*(ε*‖u‖)^2) := mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr hε.le)
      _ = P/2*‖u‖^2*ε := by field_simp
      _ ≤ Dg*ε := by
        dsimp only [Dg]
        nlinarith only [mul_le_mul_of_nonneg_left hs (by positivity : 0≤P/2*ε)]
  have ht : ‖(v,Θ)‖≤S*ε := by
    rw [Prod.norm_def,max_le_iff]
    exact ⟨hv.trans (mul_le_mul_of_nonneg_right (by dsimp only [S]; linarith only [hD]) hε.le),
      hΘ.trans (mul_le_mul_of_nonneg_right (by dsimp only [S]; linarith only [hDg]) hε.le)⟩
  have hsmall : ‖(v,Θ)‖≤δ := by
    have hh := (lt_div_iff₀ (by positivity : 0<S+1)).mp
      (he.trans_le ((min_le_right _ _).trans (min_le_right _ _)))
    exact ht.trans (by nlinarith only [hh,hε])
  have hchartA j (hj : j≤k) : rfcPhysicalSearch base Θ j=A j :=
    rfcPhysicalDataOfOperators_search base hQ A B hA hB j (by omega)
  have hchartB j (hj : j≤k) : rfcPhysicalCorrection base Θ j=B j :=
    rfcPhysicalDataOfOperators_correction base hQ A B hA hB j (by omega)
  refine ⟨hp,Θ,hchartA,hchartB,?_,ht,hsmall,hpoint⟩
  intro j hj
  exact (hp.1 j hj).2.trans (methodRun_congr_prefix _ _ _ _ _ _ _
    (fun i hi=>(hchartA i (by omega)).symm) (fun i hi=>(hchartB i (by omega)).symm))

end
end krylov.Functions
