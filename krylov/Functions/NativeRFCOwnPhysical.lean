import krylov.Functions.RFCReferenceChange

/-!
Article: main_krylov, thm:Htransfer, actual own-A₀ ordinary RFC coefficient.
Use: retain the true first search secant and observed normalized gradient in
the full physical leading response. Source: original native objective
bootstrap and the proved quadratic reference-change bound, with both source
and reference perturbations derived from genuine scalar derivatives.
-/
namespace krylov.Functions
noncomputable section
open Set Metric Matrix krylov.Methods krylov.Reference krylov.Nonlinear krylov.Correction krylov.Envelope
open scoped InnerProductSpace NNReal Matrix.Norms.L2Operator
variable {k : ℕ}

/-- Varying the matrix base adds exactly one common physical operator to
all genuine source paths. Article: main_krylov, thm:Htransfer. -/
theorem rfcPhysicalPaths_base_add
    (base Δ : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (Θ : RFCPhysicalData k) :
    (∀ i, rfcPhysicalSearch (base+Δ) Θ i=rfcPhysicalSearch base Θ i+cgOperator Δ) ∧
    (∀ i, rfcPhysicalCorrection (base+Δ) Θ i=rfcPhysicalCorrection base Θ i+cgOperator Δ) := by
  constructor <;> intro i
  · unfold rfcPhysicalSearch
    rw [show base+Δ+matrixSequenceExtension (k+1) Θ.val.1 i=
      base+matrixSequenceExtension (k+1) Θ.val.1 i+Δ by abel]
    exact map_add (Matrix.toEuclideanCLM (n:=Fin (k+1)) (𝕜:=ℝ)) _ _
  · unfold rfcPhysicalCorrection
    rw [show base+Δ+matrixSequenceExtension (k+2) Θ.val.2 i=
      base+matrixSequenceExtension (k+2) Θ.val.2 i+Δ by abel]
    exact map_add (Matrix.toEuclideanCLM (n:=Fin (k+1)) (𝕜:=ℝ)) _ _

set_option maxHeartbeats 1200000 in
/-- The true ordinary RFC terminal gradient has its actual first-secant and
observed-initial-gradient physical quadratic response, with a compact-uniform
fourth-order function remainder. Article: main_krylov, thm:Htransfer.
No original-reference error or operator output expansion is assumed. -/
theorem nativeRFC_own_physical_quadratic_remainder
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
      let ownBase := physicalOperatorMatrix (A 0)
      let ownGradient := ε⁻¹ • G (ε • u)
      ‖G (rfcFunctionPoint T f G fullMemory r (ε • u) (k+1))+
        ε • rfcPhysicalQuadratic ownBase ownGradient A B‖≤C*ε^4 := by
  let Q := cgOperator base
  obtain ⟨hQ,hpos⟩ := cgOperator_positive base hb
  obtain ⟨ep,M,D,Cp,hep,hM,hD,_,hprefix⟩ := nativeRFC_compact_prefix T hT f G H Q hr hG₀ hH₀ hHc₀
    hLr hH hF hG hQ hpos (k+1) K hK (fun g hg i hi=>hpre g hg i (by omega)) R hR
  obtain ⟨er,Cr,her,hCr,hphysical⟩ := nativeRFC_physical_quadratic_remainder base hb hk T hT f G H
    hr hG₀ hH₀ hHc₀ hLr hH hF hG K hK hpre R hR
  obtain ⟨δ,Ca,hδ,hCa,hchange⟩ := compact_rfcPhysicalQuadratic_reference_change base hb K hK hpre
  let P : ℝ := (((‖T.toContinuousLinearMap‖₊^3*L : ℝ≥0) : ℝ))
  let Dg := P/2*R^2
  let Dt := Dg+D+1
  have hP : 0≤P := NNReal.coe_nonneg _
  have hDg : 0≤Dg := by dsimp only [Dg]; positivity
  have hDt : 0<Dt := by dsimp only [Dt]; positivity
  let ε₀ := min er (min ep (min (r/(‖T.toContinuousLinearMap‖*M+1)) (δ/(Dt+1))))
  have hε₀ : 0<ε₀ := by dsimp only [ε₀]; positivity
  refine ⟨ε₀,Cr+Ca*Dt*D^2,hε₀,by positivity,?_⟩
  intro ε hε he u hu hKu
  have hp := hprefix ε hε (he.trans_le ((min_le_right _ _).trans (min_le_left _ _))) u hu hKu
  let x₀ := ε • u
  let A := rfcFunctionSearchOperator T f G H fullMemory r x₀
  let B := rfcFunctionCorrectionOperator T f G H fullMemory r x₀
  have hscale : ‖T.toContinuousLinearMap‖*(M*ε)<r := by
    have hh := (lt_div_iff₀ (by positivity : 0<‖T.toContinuousLinearMap‖*M+1)).mp
      (he.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
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
  let Δ := physicalOperatorMatrix (A 0-Q)
  have hΔ : ‖Δ‖≤D*ε := by rw [show Δ=physicalOperatorMatrix (A 0-Q) from rfl,physicalOperatorMatrix_norm]; exact (hp.2 0 (by omega)).1
  have hbase : base+Δ=physicalOperatorMatrix (A 0) := by
    apply (Matrix.toEuclideanCLM (n:=Fin (k+1)) (𝕜:=ℝ)).injective
    change cgOperator (base+Δ)=cgOperator (physicalOperatorMatrix (A 0))
    rw [physicalOperatorMatrix_operator]
    rw [show cgOperator (base+Δ)=cgOperator base+cgOperator Δ from
      map_add (Matrix.toEuclideanCLM (n:=Fin (k+1)) (𝕜:=ℝ)) base Δ]
    rw [show cgOperator Δ=A 0-Q from physicalOperatorMatrix_operator _]
    dsimp only [Q]
    abel
  have ht : ‖(Δ,v)‖≤Dt*ε := by
    rw [Prod.norm_def,max_le_iff]
    exact ⟨hΔ.trans (mul_le_mul_of_nonneg_right (by dsimp only [Dt]; linarith only [hDg]) hε.le),
      hv.trans (mul_le_mul_of_nonneg_right (by dsimp only [Dt]; linarith only [hD]) hε.le)⟩
  have hsmall : ‖(Δ,v)‖≤δ := by
    have hh := (lt_div_iff₀ (by positivity : 0<Dt+1)).mp
      (he.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
    exact ht.trans (by nlinarith only [hh,hε])
  have hc := hchange (Q u) hKu Δ v hsmall Θ
  have hcoeff (b : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (g : EuclideanSpace ℝ (Fin (k+1))) :
      rfcPhysicalQuadratic b g (rfcPhysicalSearch base Θ) (rfcPhysicalCorrection base Θ)=rfcPhysicalQuadratic b g A B :=
    rfcPhysicalQuadratic_congr_prefix b g _ _ A B
      (fun j hj=>rfcPhysicalDataOfOperators_search base hQ A B hA hB j (by omega))
      (rfcPhysicalDataOfOperators_correction base hQ A B hA hB k (by omega))
  have hpA := (rfcPhysicalPaths_base_add base Δ Θ).1
  have hpB := (rfcPhysicalPaths_base_add base Δ Θ).2
  have hpathA : rfcPhysicalSearch (base+Δ) Θ=fun i=>rfcPhysicalSearch base Θ i+cgOperator Δ := funext hpA
  have hpathB : rfcPhysicalCorrection (base+Δ) Θ=fun i=>rfcPhysicalCorrection base Θ i+cgOperator Δ := funext hpB
  rw [hpathA,hpathB,rfcPhysicalQuadratic_common_shift,hcoeff,hcoeff,hbase] at hc
  have hg : Q u+v=ε⁻¹ • G x₀ := by dsimp only [v]; abel
  rw [hg] at hc
  have hcb : ‖rfcPhysicalQuadratic (physicalOperatorMatrix (A 0)) (ε⁻¹ • G x₀) A B-
      rfcPhysicalQuadratic base (Q u) A B‖≤Ca*Dt*D^2*ε^3 := by
    exact hc.trans ((mul_le_mul
      (mul_le_mul_of_nonneg_left ht hCa.le)
      (pow_le_pow_left₀ (norm_nonneg _) hΘ 2) (by positivity) (by positivity)).trans_eq (by ring))
  have hr0 := hphysical ε hε (he.trans_le (min_le_left _ _)) u hu hKu
  have heq : G (rfcFunctionPoint T f G fullMemory r x₀ (k+1))+
      ε • rfcPhysicalQuadratic (physicalOperatorMatrix (A 0)) (ε⁻¹ • G x₀) A B=
      (G (rfcFunctionPoint T f G fullMemory r x₀ (k+1))+ε • rfcPhysicalQuadratic base (Q u) A B)+
        ε • (rfcPhysicalQuadratic (physicalOperatorMatrix (A 0)) (ε⁻¹ • G x₀) A B-rfcPhysicalQuadratic base (Q u) A B) := by module
  change ‖G (rfcFunctionPoint T f G fullMemory r x₀ (k+1))+ε • rfcPhysicalQuadratic (physicalOperatorMatrix (A 0)) (ε⁻¹ • G x₀) A B‖≤_
  rw [heq]
  apply (norm_add_le _ _).trans
  rw [norm_smul,Real.norm_of_nonneg hε.le]
  exact (add_le_add hr0 (mul_le_mul_of_nonneg_left hcb hε.le)).trans_eq (by ring)

end
end krylov.Functions
