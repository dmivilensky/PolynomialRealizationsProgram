import krylov.Functions.NativeRFCFPhysicalTransfer

/-!
Article: main_krylov, prop:Fcycle(ii), genuine cubic RFC-F cycle bounds.
Use: bound the actually returned gradient and point from primitive scalar
function data. The quadratic source bound is the norm of the true bounded
bilinear response; no leading-gradient or output-size estimate is assumed.
Source: the genuine physical fourth-order remainder, actual value-model
bootstrap and the local gradient Taylor theorem.
-/
namespace krylov.Functions
noncomputable section
open Set Metric Matrix krylov.Methods krylov.Reference krylov.Nonlinear krylov.Correction
  krylov.Envelope krylov.Secant krylov.Variation chebyshev1.Nonlinear
open scoped InnerProductSpace NNReal Matrix.Norms.L2Operator
variable {k : ℕ}

set_option maxHeartbeats 1000000 in
/-- The actual native RFC-F gradient has a compact-uniform cubic bound.
Article: main_krylov, prop:Fcycle(ii). -/
theorem nativeRFCF_gradient_cubic
    (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef) (hk : 0<k)
    (T : EuclideanSpace ℝ (Fin (k+1)) ≃L[ℝ] EuclideanSpace ℝ (Fin (k+1)))
    (hT : T.symm.toContinuousLinearMap.IsSymmetric)
    (f : EuclideanSpace ℝ (Fin (k+1)) → ℝ)
    (G : EuclideanSpace ℝ (Fin (k+1)) → EuclideanSpace ℝ (Fin (k+1)))
    (H : EuclideanSpace ℝ (Fin (k+1)) → EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1)))
    (D₃ : EuclideanSpace ℝ (Fin (k+1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1)))
    (hD₃ : HasFDerivAt H D₃ 0)
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
      ‖G (rfcFPoint T f G r (ε • u) k)‖≤C*ε^3 := by
  obtain ⟨er,Cr,her,hCr,hrem⟩ := nativeRFCF_physical_quadratic_remainder base hb hk T hT f G H
    D₃ hD₃ hr hG₀ hH₀ hHc₀ hLr hH hF hG K hK hpre R hR
  obtain ⟨ei,M,D,C,S,CF,hei,hM,hD,hC,hS,hCF,hinput⟩ := nativeRFCF_compact_inputs base hb hk T hT f G H
    D₃ hD₃ hr hG₀ hH₀ hHc₀ hLr hH hF hG K hK hpre R 1 hR (by norm_num)
  obtain ⟨Mq,hMq,hquad⟩ := compact_rfcModifiedQuadratic_norm base hb K hK hpre
  refine ⟨min er (min ei 1),Cr+Mq*S^2+1,by positivity,by positivity,?_⟩
  intro ε hε he u hu hKu
  have he1 : ε≤1 := he.le.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨_,Θ,hA,hB,hhistory,_,_,hsource,_,_,_⟩ := hinput ε hε
    (he.trans_le ((min_le_right _ _).trans (min_le_left _ _))) u hu hKu
  let gn := ε⁻¹ • G (ε • u)
  let α := rfcPhysicalLineScale base (gn,Θ)
  let Δ := rfcFNormalizedRawValueChange T f G r (ε • u) k ε (Fin.cons α (fun _=>1))
  have hαdict : rfcFActualLineScale T f G H r (ε • u) k=α := by
    dsimp only [rfcFActualLineScale]
    rw [←hA k le_rfl,hhistory k (by omega)]
    change rfcPhysicalLineScale base (G (ε • u),Θ)=α
    have hs : G (ε • u)=ε • gn := by
      dsimp only [gn]; rw [smul_smul,mul_inv_cancel₀ hε.ne',one_smul]
    rw [hs,rfcPhysicalLineScale_scalar base gn Θ ε hε.ne']
  have hΘ : ‖(Θ,Δ)‖≤S*ε := (norm_snd_le _).trans hsource
  have hq := (hquad (cgOperator base u) hKu (Θ,Δ)).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hΘ 2) hMq)
  have hcoef := rfcModifiedQuadratic_congr_prefix base (cgOperator base u)
    (rfcPhysicalSearch base Θ) (rfcPhysicalCorrection base Θ)
    (rfcFunctionSearchOperator T f G H fullMemory r (ε • u))
    (rfcFunctionCorrectionOperator T f G H fullMemory r (ε • u)) Δ hA (hB k le_rfl)
  rw [hcoef] at hq
  have hrsp := hrem ε hε (he.trans_le (min_le_left _ _)) u hu hKu
  dsimp only at hrsp
  rw [hαdict] at hrsp
  have hn := norm_le_norm_sub_add (G (rfcFPoint T f G r (ε • u) k))
    (-(ε • rfcModifiedQuadratic base (cgOperator base u)
      (rfcFunctionSearchOperator T f G H fullMemory r (ε • u))
      (rfcFunctionCorrectionOperator T f G H fullMemory r (ε • u)) Δ))
  simp only [sub_neg_eq_add,norm_neg] at hn
  rw [norm_smul,Real.norm_of_nonneg hε.le] at hn
  have hε4 : ε^4≤ε^3 := by nlinarith only [mul_le_mul_of_nonneg_right he1 (pow_nonneg hε.le 3)]
  exact hn.trans ((add_le_add hrsp (mul_le_mul_of_nonneg_left hq hε.le)).trans
    (by nlinarith [mul_le_mul_of_nonneg_left hε4 hCr.le,pow_pos hε 3]))


set_option maxHeartbeats 1000000 in
/-- The actual RFC-F point has compact-uniform cubic error in the true fixed
Hessian metric. Article: main_krylov, prop:Fcycle(ii).
The genuine final query is first enclosed quadratically. The actual Hessian
Taylor theorem then compares its measured gradient to its true error, with
a fourth-order discrepancy, preserving the cubic cycle exponent. -/
theorem nativeRFCF_error_cubic
    (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef) (hk : 0<k)
    (T : EuclideanSpace ℝ (Fin (k+1)) ≃L[ℝ] EuclideanSpace ℝ (Fin (k+1)))
    (hT : T.symm.toContinuousLinearMap.IsSymmetric)
    (f : EuclideanSpace ℝ (Fin (k+1)) → ℝ)
    (G : EuclideanSpace ℝ (Fin (k+1)) → EuclideanSpace ℝ (Fin (k+1)))
    (H : EuclideanSpace ℝ (Fin (k+1)) → EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1)))
    (D₃ : EuclideanSpace ℝ (Fin (k+1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1)))
    (hD₃ : HasFDerivAt H D₃ 0)
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
      ‖T (rfcFPoint T f G r (ε • u) k)‖≤C*ε^3 := by
  obtain ⟨eg,Cg,heg,hCg,hgrad⟩ := nativeRFCF_gradient_cubic base hb hk T hT f G H
    D₃ hD₃ hr hG₀ hH₀ hHc₀ hLr hH hF hG K hK hpre R hR
  obtain ⟨ei,M,D,C,S,CF,hei,hM,hD,hC,hS,hCF,hinput⟩ := nativeRFCF_compact_inputs base hb hk T hT f G H
    D₃ hD₃ hr hG₀ hH₀ hHc₀ hLr hH hF hG K hK hpre R 1 hR (by norm_num)
  let A := ((k:ℝ)+2)*C+CF
  let P : ℝ := (((‖T.toContinuousLinearMap‖₊^3*L : ℝ≥0) : ℝ))
  let Cg' := ‖T.symm.toContinuousLinearMap‖*Cg
  let Ce := ‖T.symm.toContinuousLinearMap‖*P/2*A^2
  have hA : 0<A := by dsimp only [A]; positivity
  have hP : 0≤P := NNReal.coe_nonneg _
  have hCe : 0≤Ce := by dsimp only [Ce]; positivity
  refine ⟨min eg (min ei (min 1 (r/(‖T.toContinuousLinearMap‖*A+1)))),
    Cg'+Ce+1,by positivity,by dsimp only [Cg']; positivity,?_⟩
  intro ε hε he u hu hKu
  have he_tail := he.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have he1 : ε≤1 := he_tail.le.trans (min_le_left _ _)
  have hε2 : ε^2≤ε := by nlinarith only [hε,he1]
  have hε4 : ε^4≤ε^3 := by nlinarith only [mul_le_mul_of_nonneg_right he1 (pow_nonneg hε.le 3)]
  obtain ⟨hp,_,_,_,_,_,_,_,_,_,hstep⟩ := hinput ε hε
    (he.trans_le ((min_le_right _ _).trans (min_le_left _ _))) u hu hKu
  let x := rfcFPoint T f G r (ε • u) k
  have hanchor := hp.rfcF_reference_anchor T f G H (cgOperator base) r u ε M D C k
  rw [fcQuadraticReferencePoint_full_zero base hb u,smul_zero,sub_zero] at hanchor
  have hsize : ‖x‖≤A*ε^2 :=
    (norm_add_le _ _).trans ((add_le_add hanchor hstep).trans_eq (by dsimp only [A]; ring))
  have hxr : ‖T x‖≤r := by
    have hs := (lt_div_iff₀ (by positivity : 0<‖T.toContinuousLinearMap‖*A+1)).mp
      (he_tail.trans_le (min_le_right _ _))
    have hh := (T.toContinuousLinearMap.le_opNorm x).trans
      (mul_le_mul_of_nonneg_left hsize (norm_nonneg _))
    have ht := mul_le_mul_of_nonneg_left hε2 (by positivity : 0≤‖T.toContinuousLinearMap‖*A)
    exact hh.trans (by nlinarith only [hs,ht,hε])
  have hQ (z : EuclideanSpace ℝ (Fin (k+1))) : T.symm (cgOperator base z)=T z := by
    have hz := congrArg (fun B=>B (T z)) hHc₀
    simpa only [coordinateDerivative,map_zero,hH₀,ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe,T.symm_apply_apply,ContinuousLinearMap.id_apply] using hz
  have htaylor := metric_gradient_quadratic_error T G H (cgOperator base) hr.le hG₀ hH₀ hH hG x hxr
  have hdiff := (T.symm.toContinuousLinearMap.le_opNorm (G x-cgOperator base x)).trans
    (mul_le_mul_of_nonneg_left htaylor (norm_nonneg _))
  simp only [map_sub,ContinuousLinearEquiv.coe_coe,hQ] at hdiff
  have hdif4 : ‖T.symm (G x)-T x‖≤Ce*ε^4 := by
    apply hdiff.trans
    change ‖T.symm.toContinuousLinearMap‖*(P/2*‖x‖^2)≤Ce*ε^4
    calc
      _ ≤ ‖T.symm.toContinuousLinearMap‖*(P/2*(A*ε^2)^2) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hsize 2) (by positivity)) (norm_nonneg _)
      _ = Ce*ε^4 := by dsimp only [Ce]; ring
  have hmismatch : ‖T x-T.symm (G x)‖≤Ce*ε^3 := by
    rw [norm_sub_rev]
    exact hdif4.trans (mul_le_mul_of_nonneg_left hε4 hCe)
  have hg := (T.symm.toContinuousLinearMap.le_opNorm (G x)).trans
    (mul_le_mul_of_nonneg_left (hgrad ε hε (he.trans_le (min_le_left _ _)) u hu hKu) (norm_nonneg _))
  have hn := norm_le_norm_sub_add (T x) (T.symm (G x))
  exact hn.trans ((add_le_add hmismatch hg).trans (by dsimp only [Cg']; nlinarith [pow_pos hε 3]))

end
end krylov.Functions
