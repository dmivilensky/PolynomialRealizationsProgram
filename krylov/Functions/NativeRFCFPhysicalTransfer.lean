import krylov.Functions.RFCFTerminalComparison
import krylov.Functions.RFCModifiedBilinear

/-!
Article: main_krylov, prop:Fcycle, genuine native RFC-F physical expansion.
Use: substitute the actual unchanged RFC prefix and actual value-corrected
last model into the true modified physical theorem. The new final gradient
is evaluated at the actual changed point. Its replacement of the old actually
observed correction secant costs fourth order, proved on real small endpoints.
Source: complete native value-model inputs, compact genuine modified expansion
and the true terminal-query comparison.
-/
namespace krylov.Functions
noncomputable section
open Set Metric Matrix krylov.Methods krylov.Reference krylov.Nonlinear krylov.Correction
  krylov.Envelope krylov.Secant krylov.Variation chebyshev1.Nonlinear
open scoped InnerProductSpace NNReal Matrix.Norms.L2Operator
variable {k : ℕ}

/-- The actual searched-segment quotient preceding the changed final correction.
Article: main_krylov, prop:Fcycle. -/
def rfcFActualLineScale {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (T : E ≃L[ℝ] E) (f : E → ℝ) (G : E → E) (H : E → E →L[ℝ] E)
    (r : ℝ) (x₀ : E) (k : ℕ) : ℝ :=
  let S := rfcFunctionRun T f G fullMemory r x₀ k
  let d := rfcFunctionDirection fullMemory S
  lineLength S.gradient d (rfcFunctionSearchOperator T f G H fullMemory r x₀ k d)

/-- Full-dimensional actual quadratic reference points terminate at the true minimizer.
Article: main_krylov, prop:Fcycle, reference terminal localization. -/
theorem fcQuadraticReferencePoint_full_zero
    (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (u : EuclideanSpace ℝ (Fin (k+1))) :
    fcQuadraticReferencePoint (cgOperator base) u (k+1)=0 := by
  obtain ⟨hQ,hpos⟩ := cgOperator_positive base hb
  have hgrad : CG.gradient (cgOperator base) (cgOperator base u) (k+1)=0 := by
    simpa only [finrank_euclideanSpace,Fintype.card_fin] using
      cg_gradient_finrank_zero (cgOperator base) hQ hpos (cgOperator base u)
  have hzero : cgOperator base (fcQuadraticReferencePoint (cgOperator base) u (k+1))=0 := by
    rw [fcQuadraticReferencePoint_gradient,hgrad]
  by_contra hn
  have hp := hpos _ hn
  rw [hzero,inner_zero_right] at hp
  exact lt_irrefl _ hp

set_option maxHeartbeats 800000 in
/-- The true modified physical coefficient reads exactly its real executed operator prefix.
Article: main_krylov, prop:Fcycle, genuine finite-chart dictionary. -/
theorem rfcModifiedQuadratic_congr_prefix (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ)
    (g : EuclideanSpace ℝ (Fin (k+1)))
    (A B A' B' : ℕ → EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1)))
    (D : Matrix (Fin (k+1)) (Fin (k+1)) ℝ)
    (hA : ∀ j≤k,A j=A' j) (hB : B k=B' k) :
    rfcModifiedQuadratic base g A B D=rfcModifiedQuadratic base g A' B' D := by
  let U := referenceModelBasis base g k
  have hL : (Matrix.of fun i j : Fin (k+1)=>inner ℝ (U i) ((B k-A (k-(min i j).val)) (U j)))=
      (Matrix.of fun i j : Fin (k+1)=>inner ℝ (U i) ((B' k-A' (k-(min i j).val)) (U j))) := by
    ext i j
    simp only [Matrix.of_apply,hB,hA _ (Nat.sub_le _ _)]
  have hf : frozenIncoming (cgOperator base) g A k=frozenIncoming (cgOperator base) g A' k := by
    unfold frozenIncoming
    congr 1
    funext i
    refine Fin.cases rfl (fun j=>?_) i
    simp only [Fin.cons_succ,hA k le_rfl]
    rw [hA _ (by omega)]
  dsimp only [rfcModifiedQuadratic]
  rw [hf]
  change cgOperator ((fullBasisMatrix U)ᵀ⁻¹*(((Matrix.of fun i j : Fin (k+1)=>
    inner ℝ (U i) ((B k-A (k-(min i j).val)) (U j)))-D)*_)) _=_
  rw [hL]

set_option maxHeartbeats 1400000 in
/-- The actual value-corrected scalar-function RFC-F output has its genuine
physical quadratic coefficient and a compact-uniform fourth-order cycle remainder.
Article: main_krylov, prop:Fcycle(i).
The physical operators, observed scalar diagonal, original gate, true query
localization and new returned gradient are all derived from primitive function data. -/
theorem nativeRFCF_physical_quadratic_remainder
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
    ∃ ε₀ C : ℝ,0<ε₀ ∧ 0<C ∧ ∀ ε : ℝ,0<ε → ε<ε₀ →
      ∀ u : EuclideanSpace ℝ (Fin (k+1)),‖u‖≤R → cgOperator base u∈K →
      let α := rfcFActualLineScale T f G H r (ε • u) k
      let Δ := rfcFNormalizedRawValueChange T f G r (ε • u) k ε (Fin.cons α (fun _=>1))
      ‖G (rfcFPoint T f G r (ε • u) k)+ε • rfcModifiedQuadratic base (cgOperator base u)
        (rfcFunctionSearchOperator T f G H fullMemory r (ε • u))
        (rfcFunctionCorrectionOperator T f G H fullMemory r (ε • u)) Δ‖≤C*ε^4 := by
  let Q := cgOperator base
  obtain ⟨δ,Cq,hδ,hCq,hresponse⟩ := compact_rfc_modified_quadratic base hb hk K hK hpre
  obtain ⟨ep,M,D,Cp,S,CF,hep,hM,hD,hCp,hS,hCF,hinput⟩ := nativeRFCF_compact_inputs base hb hk T hT f G H
    D₃ hD₃ hr hG₀ hH₀ hHc₀ hLr hH hF hG K hK hpre R δ hR hδ
  let Aterm := ((k:ℝ)+2)*Cp
  let Bterm := ((k:ℝ)+1)*Cp
  let P : ℝ := (((‖T.toContinuousLinearMap‖₊^3*L : ℝ≥0) : ℝ))
  let Ct := P/2*((Aterm+CF)^2+Aterm^2+(Aterm+Bterm)*CF)
  let Cd := Ct+Cq*S^3+1
  let ε₀ := min ep (min 1 (r/(2*(‖T.toContinuousLinearMap‖*(Aterm+Bterm+CF+M+1)+1))))
  have hAterm : 0<Aterm := by dsimp only [Aterm]; positivity
  have hBterm : 0<Bterm := by dsimp only [Bterm]; positivity
  have hP : 0≤P := NNReal.coe_nonneg _
  have hCt : 0≤Ct := by dsimp only [Ct]; positivity
  have hCd : 0<Cd := by dsimp only [Cd]; positivity
  have hε₀ : 0<ε₀ := by dsimp only [ε₀]; positivity
  refine ⟨ε₀,Cd,hε₀,hCd,?_⟩
  intro ε hε he u hu hKu
  obtain ⟨hp,Θ,hA,hB,hhistory,hα,hgate,hsource,hsmall,hstep,hnorm⟩ := hinput ε hε
    (he.trans_le (min_le_left _ _)) u hu hKu
  let x₀ := ε • u
  let gn := ε⁻¹ • G x₀
  let v := gn-Q u
  let AP := rfcPhysicalSearch base Θ
  let BP := rfcPhysicalCorrection base Θ
  let α := rfcPhysicalLineScale base (gn,Θ)
  let Δ := rfcFNormalizedRawValueChange T f G r x₀ k ε (Fin.cons α (fun _=>1))
  let Y := rfcFAnchor T f G r x₀ k
  let X := rfcFunctionPoint T f G fullMemory r x₀ (k+1)
  let U := rfcFCorrectionStep T f G r x₀ k
  have hgn : Q u+v=gn := by dsimp only [v]; abel
  have hscaleG : G x₀=ε • gn := by dsimp only [gn]; rw [smul_smul,mul_inv_cancel₀ hε.ne',one_smul]
  have hαdict : rfcFActualLineScale T f G H r x₀ k=α := by
    dsimp only [rfcFActualLineScale]
    rw [←hA k le_rfl,hhistory k (by omega)]
    change rfcPhysicalLineScale base (G x₀,Θ)=α
    rw [hscaleG,rfcPhysicalLineScale_scalar base gn Θ ε hε.ne']
  have hY : ‖Y‖≤Aterm*ε^2 := by
    have hh := hp.rfcF_reference_anchor T f G H Q r u ε M D Cp k
    rw [show fcQuadraticReferencePoint Q u (k+1)=0 from fcQuadraticReferencePoint_full_zero base hb u,
      smul_zero,sub_zero] at hh
    exact hh
  have hX : ‖X‖≤Bterm*ε^2 := by
    have hh := hp.reference_points T f G H Q r u ε M D Cp (k+1) (k+1) le_rfl
    rw [show fcQuadraticReferencePoint Q u (k+1)=0 from fcQuadraticReferencePoint_full_zero base hb u,
      smul_zero,sub_zero] at hh
    simpa only [Nat.cast_add,Nat.cast_one] using hh
  have hU : ‖U‖≤CF*ε^2 := hnorm
  have hε1 : ε≤1 := (he.trans_le ((min_le_right _ _).trans (min_le_left _ _))).le
  have he2 : ε^2≤ε := by nlinarith only [hε,hε1]
  have hscale : ‖T.toContinuousLinearMap‖*(Aterm+Bterm+CF+M+1)*ε<r/2 := by
    have hh := (lt_div_iff₀ (by positivity : 0<2*(‖T.toContinuousLinearMap‖*(Aterm+Bterm+CF+M+1)+1))).mp
      (he.trans_le ((min_le_right _ _).trans (min_le_right _ _)))
    nlinarith only [hh,hε]
  have hYr : ‖T Y‖≤r := by
    have hn := (T.toContinuousLinearMap.le_opNorm Y).trans (mul_le_mul_of_nonneg_left hY (norm_nonneg _))
    have ht := mul_le_mul_of_nonneg_left he2 (by positivity : 0≤‖T.toContinuousLinearMap‖*Aterm)
    have hbig := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (by linarith : Aterm≤Aterm+Bterm+CF+M+1) (norm_nonneg T.toContinuousLinearMap)) hε.le
    exact hn.trans (by
      calc
        ‖T.toContinuousLinearMap‖*(Aterm*ε^2)=‖T.toContinuousLinearMap‖*Aterm*ε^2 := by ring
        _ ≤ ‖T.toContinuousLinearMap‖*Aterm*ε := ht
        _ ≤ ‖T.toContinuousLinearMap‖*(Aterm+Bterm+CF+M+1)*ε := hbig
        _ ≤ r := hscale.le.trans (by linarith only [hr]))
  have hXr : ‖T X‖≤r := by
    have hn := (T.toContinuousLinearMap.le_opNorm X).trans (mul_le_mul_of_nonneg_left hX (norm_nonneg _))
    have ht := mul_le_mul_of_nonneg_left he2 (by positivity : 0≤‖T.toContinuousLinearMap‖*Bterm)
    have hbig := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (by linarith : Bterm≤Aterm+Bterm+CF+M+1) (norm_nonneg T.toContinuousLinearMap)) hε.le
    exact hn.trans (by
      calc
        ‖T.toContinuousLinearMap‖*(Bterm*ε^2)=‖T.toContinuousLinearMap‖*Bterm*ε^2 := by ring
        _ ≤ ‖T.toContinuousLinearMap‖*Bterm*ε := ht
        _ ≤ ‖T.toContinuousLinearMap‖*(Aterm+Bterm+CF+M+1)*ε := hbig
        _ ≤ r := hscale.le.trans (by linarith only [hr]))
  have hFpoint : ‖Y+U‖≤(Aterm+CF)*ε^2 :=
    (norm_add_le _ _).trans ((add_le_add hY hU).trans_eq (by ring))
  have hFmetric : ‖T (Y+U)‖≤r := by
    have hn := (T.toContinuousLinearMap.le_opNorm _).trans (mul_le_mul_of_nonneg_left hFpoint (norm_nonneg _))
    have ht := mul_le_mul_of_nonneg_left he2 (by positivity : 0≤‖T.toContinuousLinearMap‖*(Aterm+CF))
    have hbig := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (by linarith : Aterm+CF≤Aterm+Bterm+CF+M+1) (norm_nonneg T.toContinuousLinearMap)) hε.le
    exact hn.trans (by
      calc
        ‖T.toContinuousLinearMap‖*((Aterm+CF)*ε^2)=‖T.toContinuousLinearMap‖*(Aterm+CF)*ε^2 := by ring
        _ ≤ ‖T.toContinuousLinearMap‖*(Aterm+CF)*ε := ht
        _ ≤ ‖T.toContinuousLinearMap‖*(Aterm+Bterm+CF+M+1)*ε := hbig
        _ ≤ r := hscale.le.trans (by linarith only [hr]))
  have hBold : BP k=averagedDerivative H Y (X-Y) := by
    change rfcPhysicalCorrection base Θ k=averagedDerivative H Y (X-Y)
    rw [hB k le_rfl]
    change averagedDerivative H Y (rfcFunctionCorrectionStep T f G fullMemory r x₀
      (rfcFunctionRun T f G fullMemory r x₀ k))=averagedDerivative H Y (X-Y)
    have hXY : X-Y=rfcFunctionCorrectionStep T f G fullMemory r x₀
        (rfcFunctionRun T f G fullMemory r x₀ k) := by
      dsimp only [X,Y,rfcFAnchor]
      rw [rfcFunctionPoint_succ_line,add_sub_cancel_left]
    rw [hXY]
  have herror := metric_terminal_query_comparison T G H Q hr.le hG₀ hH₀ hH hG Y X U hYr hXr hFmetric
    Aterm Bterm CF (ε^2) hAterm.le hBterm.le (sq_nonneg ε) hY hX hU
  rw [←hBold] at herror
  have herror' : ‖G (Y+U)-(G Y+BP k U)‖≤Ct*ε^4 := by
    exact herror.trans_eq (by dsimp only [Ct,P]; ring)
  have hcurrent : ‖T (rfcFunctionPoint T f G fullMemory r x₀ k)‖<r/2 := by
    have hn := (T.toContinuousLinearMap.le_opNorm _).trans
      (mul_le_mul_of_nonneg_left (hp.1 k (by omega)).1 (norm_nonneg _))
    have hbig := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (by linarith : M≤Aterm+Bterm+CF+M+1) (norm_nonneg T.toContinuousLinearMap)) hε.le
    exact hn.trans_lt (by
      calc
        ‖T.toContinuousLinearMap‖*(M*ε)=‖T.toContinuousLinearMap‖*M*ε := by ring
        _ ≤ ‖T.toContinuousLinearMap‖*(Aterm+Bterm+CF+M+1)*ε := hbig
        _ < r/2 := hscale)
  have hline := (rfcFunctionLine_operator T hT f G H hr hG₀ hHc₀ hLr hH hF hG fullMemory x₀
    (rfcFunctionRun T f G fullMemory r x₀ k) (rfcFunctionRun_gradient T f G fullMemory r x₀ k) hcurrent).2
  have hpost : G Y=fullPostSearch 1 AP BP (G x₀) k := by
    rw [show Y=rfcFunctionLinePoint T f fullMemory r x₀ (rfcFunctionRun T f G fullMemory r x₀ k) from rfl,hline]
    change searchedGradient (rfcFunctionRun T f G fullMemory r x₀ k).gradient
      (rfcFunctionDirection fullMemory (rfcFunctionRun T f G fullMemory r x₀ k))
      (rfcFunctionSearchOperator T f G H fullMemory r x₀ k
        (rfcFunctionDirection fullMemory (rfcFunctionRun T f G fullMemory r x₀ k)))=_
    have hAk : rfcFunctionSearchOperator T f G H fullMemory r x₀ k=AP k := (hA k le_rfl).symm
    rw [hAk,hhistory k (by omega)]
    rfl
  have hfake : G Y+BP k U=ε • modifiedTerminalGradient AP BP gn k Δ := by
    have hstep' : U=ε • rfcModifiedCorrection AP BP gn Δ := hstep
    rw [hpost,hscaleG,rfc_fullPostSearch_scalar AP BP gn ε hε.ne',hstep',map_smul,←smul_add]
    rfl
  have hrsp := hresponse (Q u) hKu v Θ Δ hsmall
  rw [hgn] at hrsp
  have hfakeBound : ‖G Y+BP k U+ε • rfcModifiedQuadratic base (Q u) AP BP Δ‖≤Cq*S^3*ε^4 := by
    rw [hfake,←smul_add,norm_smul,Real.norm_of_nonneg hε.le]
    have hpw := pow_le_pow_left₀ (norm_nonneg _) hsource 3
    exact (mul_le_mul_of_nonneg_left (hrsp.trans (mul_le_mul_of_nonneg_left hpw hCq)) hε.le).trans_eq (by ring)
  have hcoef := rfcModifiedQuadratic_congr_prefix base (Q u) AP BP
    (rfcFunctionSearchOperator T f G H fullMemory r x₀)
    (rfcFunctionCorrectionOperator T f G H fullMemory r x₀) Δ hA (hB k le_rfl)
  have heq : G (Y+U)+ε • rfcModifiedQuadratic base (Q u) AP BP Δ=
      (G (Y+U)-(G Y+BP k U))+(G Y+BP k U+ε • rfcModifiedQuadratic base (Q u) AP BP Δ) := by abel
  change ‖G (Y+U)+ε • rfcModifiedQuadratic base (Q u) _ _ _‖≤Cd*ε^4
  rw [hαdict,←hcoef,heq]
  exact (norm_add_le _ _).trans
    ((add_le_add herror' hfakeBound).trans (by dsimp only [Cd]; nlinarith only [sq_nonneg (ε^2)]))

end
end krylov.Functions
