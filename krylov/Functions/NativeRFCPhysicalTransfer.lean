import krylov.Functions.NativeRFCPhysicalInputs

/-!
Article: main_krylov, thm:Htransfer, native ordinary RFC physical expansion.
Use: substitute the true objective executor into the compact physical RFC
expansion, retaining the actual initial gradient and actual first search
secant. Source: the fully derived native bootstrap, actual symmetric source
coordinates, genuine homogeneity and the compact cubic operator remainder.
-/
namespace krylov.Functions
noncomputable section
open Set Metric Matrix krylov.Methods krylov.Reference krylov.Nonlinear krylov.Correction
open scoped InnerProductSpace NNReal Matrix.Norms.L2Operator
variable {k : ℕ}

set_option maxHeartbeats 800000 in
/-- The genuine native ordinary RFC terminal gradient has its true frozen
physical quadratic response with a uniform fourth-order cycle remainder.
Article: main_krylov, thm:Htransfer.
All physical query operators below are the actual Hessian averages of the
actual objective algorithm. Their first-order tensor jets are derived in
NativeRFCJets and may be substituted into this exact quadratic response.
No native trajectory bounds, oracle identities or output expansion are assumed. -/
theorem nativeRFC_physical_quadratic_remainder
    (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef) (hk : 0<k)
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
    (R : ℝ) (hR : 0<R) :
    ∃ ε₀ C : ℝ, 0<ε₀ ∧ 0<C ∧ ∀ ε : ℝ, 0<ε → ε<ε₀ →
      ∀ u : EuclideanSpace ℝ (Fin (k+1)), ‖u‖≤R → cgOperator base u∈K →
      let A := rfcFunctionSearchOperator T f G H fullMemory r (ε • u)
      let B := rfcFunctionCorrectionOperator T f G H fullMemory r (ε • u)
      ‖G (rfcFunctionPoint T f G fullMemory r (ε • u) (k+1))+
        ε • rfcPhysicalQuadratic base (cgOperator base u) A B‖≤C*ε^4 := by
  let Q := cgOperator base
  obtain ⟨hQ,hpos⟩ := cgOperator_positive base hb
  obtain ⟨ep,M,D,Cp,hep,hM,hD,_,hprefix⟩ := nativeRFC_compact_prefix T hT f G H Q hr hG₀ hH₀ hHc₀
    hLr hH hF hG hQ hpos (k+1) K hK (fun g hg i hi=>hpre g hg i (by omega)) R hR
  obtain ⟨δ,C,hδ,hC,hresponse⟩ := compact_rfc_physical_quadratic base hb hk K hK hpre
  let P : ℝ := (((‖T.toContinuousLinearMap‖₊^3*L : ℝ≥0) : ℝ))
  let Dg := P/2*R^2
  let Dt := Dg+D+1
  have hP : 0≤P := NNReal.coe_nonneg _
  have hDg : 0≤Dg := by dsimp only [Dg]; positivity
  have hDt : 0<Dt := by dsimp only [Dt]; positivity
  let ε₀ := min ep (min (r/(‖T.toContinuousLinearMap‖*M+1)) (δ/(Dt+1)))
  have hε₀ : 0<ε₀ := by dsimp only [ε₀]; positivity
  refine ⟨ε₀,C*Dt^3+1,hε₀,by positivity,?_⟩
  intro ε hε he u hu hKu
  have hp := hprefix ε hε (he.trans_le (min_le_left _ _)) u hu hKu
  let x₀ := ε • u
  let A := rfcFunctionSearchOperator T f G H fullMemory r x₀
  let B := rfcFunctionCorrectionOperator T f G H fullMemory r x₀
  have hscale : ‖T.toContinuousLinearMap‖*(M*ε)<r := by
    have hh := (lt_div_iff₀ (by positivity : 0<‖T.toContinuousLinearMap‖*M+1)).mp
      (he.trans_le ((min_le_right _ _).trans (min_le_left _ _)))
    nlinarith only [hh,hε]
  have hsym := hp.operator_symmetric T f G H Q r u ε M D Cp (k+1) hscale hH hF hG
  have hA j (hj : j<k+1) : (A j).toLinearMap.IsSymmetric := (hsym j hj).1
  have hB j (hj : j<k+1) : (B j).toLinearMap.IsSymmetric := (hsym j hj).2
  let Θ := rfcPhysicalDataOfOperators base hQ A B hA hB
  have hΘ : ‖Θ‖≤D*ε := rfcPhysicalDataOfOperators_norm base hQ A B hA hB
    (D*ε) (by positivity) (fun j hj=>(hp.2 j hj).1) (fun j hj=>(hp.2 j hj).2.1)
  have hx₀ : ‖T x₀‖≤r := by
    have hx := (hp.1 0 (by omega)).1
    change ‖rfcFunctionPoint T f G fullMemory r x₀ 0‖≤M*ε at hx
    have heq : rfcFunctionPoint T f G fullMemory r x₀ 0=x₀ := by
      simp [rfcFunctionPoint,rfcFunctionRun,History.displacement]
    rw [heq] at hx
    have hn := (T.toContinuousLinearMap.le_opNorm x₀).trans
      (mul_le_mul_of_nonneg_left hx (norm_nonneg _))
    exact hn.trans hscale.le
  let v := ε⁻¹ • G x₀-Q u
  have hv : ‖v‖≤Dg*ε := by
    have hh := metric_gradient_quadratic_error T G H Q hr.le hG₀ hH₀ hH hG x₀ hx₀
    have heq : v=ε⁻¹ • (G x₀-Q x₀) := by
      dsimp only [v,x₀]
      rw [smul_sub,map_smul,smul_smul,inv_mul_cancel₀ hε.ne',one_smul]
    rw [heq,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hε.le)]
    have hs : ‖u‖^2≤R^2 := (sq_le_sq₀ (norm_nonneg _) hR.le).mpr hu
    rw [show x₀=ε • u from rfl,norm_smul,Real.norm_of_nonneg hε.le] at hh
    calc
      _ ≤ ε⁻¹*(P/2*(ε*‖u‖)^2) := mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr hε.le)
      _ = P/2*‖u‖^2*ε := by field_simp
      _ ≤ Dg*ε := by
        dsimp only [Dg]
        nlinarith only [mul_le_mul_of_nonneg_left hs (by positivity : 0≤P/2*ε)]
  have ht : ‖(v,Θ)‖≤Dt*ε := by
    rw [Prod.norm_def,max_le_iff]
    exact ⟨hv.trans (mul_le_mul_of_nonneg_right (by dsimp only [Dt]; linarith only [hD]) hε.le),
      hΘ.trans (mul_le_mul_of_nonneg_right (by dsimp only [Dt]; linarith only [hDg]) hε.le)⟩
  have hsmall : ‖(v,Θ)‖≤δ := by
    have hh := (lt_div_iff₀ (by positivity : 0<Dt+1)).mp
      (he.trans_le ((min_le_right _ _).trans (min_le_right _ _)))
    exact ht.trans (by nlinarith only [hh,hε])
  have hchartA j (hj : j<k+1) : rfcPhysicalSearch base Θ j=A j :=
    rfcPhysicalDataOfOperators_search base hQ A B hA hB j hj
  have hchartB j (hj : j<k+1) : rfcPhysicalCorrection base Θ j=B j :=
    rfcPhysicalDataOfOperators_correction base hQ A B hA hB j hj
  have hinit : G x₀=ε • (Q u+v) := by
    dsimp only [v]
    rw [add_sub_cancel,smul_smul,mul_inv_cancel₀ hε.ne',one_smul]
  have hgradient : G (rfcFunctionPoint T f G fullMemory r x₀ (k+1))=
      ε • probedGradient (rfcMethod fullMemory 1) (rfcPhysicalSearch base Θ)
        (rfcPhysicalCorrection base Θ) (Q u+v) (k+1) := by
    rw [←rfcFunctionRun_gradient T f G fullMemory r x₀ (k+1),(hp.1 (k+1) le_rfl).2]
    conv_lhs => rw [hinit]
    have hh := methodRun_congr_prefix (rfcMethod fullMemory 1) A B
      (rfcPhysicalSearch base Θ) (rfcPhysicalCorrection base Θ) (ε • (Q u+v)) (k+1)
      (fun j hj=>(hchartA j hj).symm) (fun j hj=>(hchartB j hj).symm)
    rw [hh]
    exact (rfc_scalar fullMemory 1 _ _ (Q u+v) ε hε.ne' (k+1)).1
  have hquadratic : rfcPhysicalQuadratic base (Q u) (rfcPhysicalSearch base Θ)
      (rfcPhysicalCorrection base Θ)=rfcPhysicalQuadratic base (Q u) A B :=
    rfcPhysicalQuadratic_congr_prefix base (Q u) _ _ A B (fun j hj=>hchartA j (by omega))
      (hchartB k (by omega))
  have hres := hresponse (Q u) hKu v Θ hsmall
  rw [hquadratic] at hres
  change ‖G (rfcFunctionPoint T f G fullMemory r x₀ (k+1))+ε • rfcPhysicalQuadratic base (Q u) A B‖≤_
  rw [hgradient,←smul_add,norm_smul,Real.norm_of_nonneg hε.le]
  calc
    _ ≤ ε*(C*‖(v,Θ)‖^3) := mul_le_mul_of_nonneg_left hres hε.le
    _ ≤ ε*(C*(Dt*ε)^3) := by gcongr
    _ ≤ (C*Dt^3+1)*ε^4 := by nlinarith only [sq_nonneg (ε^2)]

end
end krylov.Functions
