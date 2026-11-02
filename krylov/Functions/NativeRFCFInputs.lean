import krylov.Functions.NativeRFCPhysicalTube
import krylov.Functions.RFCFDiagonalCoordinates

/-!
Article: main_krylov, prop:Fcycle, genuine value-corrected final-query bootstrap.
Use: derive the real RFC-F correction bound from its actual unchanged prefix,
actual observed diagonal and actual accepted model solve before enclosing its
new endpoint. All compact inverse-line and diagonal source bounds are proved.
Source: true native ordinary RFC inputs, genuine C3 value jets, exact model
coordinate changes and compact analytic control of the actual modified query.
-/
namespace krylov.Functions
noncomputable section
open Set Metric Matrix krylov.Methods krylov.Reference krylov.Nonlinear krylov.Correction chebyshev1.Nonlinear
open scoped InnerProductSpace NNReal Matrix.Norms.L2Operator
variable {k : ℕ}

set_option maxHeartbeats 1200000 in
/-- Every actual native RFC-F final solve has a genuine compact physical
source and a derived quadratic correction bound, before its new gradient
query is evaluated. Article: main_krylov, prop:Fcycle.
The observed diagonal, accepted branch, raw column scale, operator chart and
full original prefix are all conclusions of the primitive function hypotheses. -/
theorem nativeRFCF_compact_inputs
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
    (R δ : ℝ) (hR : 0<R) (hδ : 0<δ) :
    ∃ ε₀ M D C S CF : ℝ, 0<ε₀ ∧ 0<M ∧ 0<D ∧ 0<C ∧ 0<S ∧ 0<CF ∧
      ∀ ε : ℝ, 0<ε → ε<ε₀ → ∀ u : EuclideanSpace ℝ (Fin (k+1)), ‖u‖≤R → cgOperator base u∈K →
      NativeRFCPrefixBounds T f G H (cgOperator base) r u ε M D C (k+1) ∧
      ∃ Θ : RFCPhysicalData k,
        (∀ j≤k, rfcPhysicalSearch base Θ j=rfcFunctionSearchOperator T f G H fullMemory r (ε • u) j) ∧
        (∀ j≤k, rfcPhysicalCorrection base Θ j=rfcFunctionCorrectionOperator T f G H fullMemory r (ε • u) j) ∧
        (∀ j≤k+1,rfcFunctionRun T f G fullMemory r (ε • u) j=
          methodRun (rfcMethod fullMemory 1) (rfcPhysicalSearch base Θ) (rfcPhysicalCorrection base Θ) (G (ε • u)) j) ∧
        let α := rfcPhysicalLineScale base (ε⁻¹ • G (ε • u),Θ)
        let Δ := rfcFNormalizedRawValueChange T f G r (ε • u) k ε (Fin.cons α (fun _=>1))
        α≠0 ∧ rfcFunctionGate fullMemory (rfcFunctionRun T f G fullMemory r (ε • u) k) ∧
        ‖(ε⁻¹ • G (ε • u)-cgOperator base u,(Θ,Δ))‖≤S*ε ∧
        ‖(ε⁻¹ • G (ε • u)-cgOperator base u,(Θ,Δ))‖≤δ ∧
        rfcFCorrectionStep T f G r (ε • u) k=ε • rfcModifiedCorrection
          (rfcPhysicalSearch base Θ) (rfcPhysicalCorrection base Θ) (ε⁻¹ • G (ε • u)) Δ ∧
        ‖rfcFCorrectionStep T f G r (ε • u) k‖≤CF*ε^2 := by
  let Q := cgOperator base
  obtain ⟨hQ,hpos⟩ := cgOperator_positive base hb
  obtain ⟨δχ,Cχ,hδχ,hCχ,hχ⟩ := compact_rfc_modified_correction base hb K hK hpre
  obtain ⟨δg,hδg,hgate⟩ := compact_rfc_physical_gate base hb hk K hK hpre
  obtain ⟨δa,Ca,Ma,hδa,hCa,hMa,ha⟩ := compact_rfc_line_inverse_square base hb K hK hpre
  obtain ⟨B,hB,hcoeff⟩ := compact_reference_cubic_bound Q hQ hpos D₃ k K hK
    (fun g hg i hi=>hpre g hg i (by omega))
  obtain ⟨ed,hed,hdiag⟩ := nativeRFCF_value_diagonal_jet T hT f G H Q D₃ hD₃ hr hG₀ hH₀ hHc₀
    hLr hH hF hG hQ hpos k K hK (fun g hg i hi=>hpre g hg i (by omega)) R hR 1 (by norm_num)
  obtain ⟨ep,M,D,C,S,hep,hM,hD,hC,hS,hinput⟩ := nativeRFC_physical_source_tube base hb T hT f G H
    hr hG₀ hH₀ hHc₀ hLr hH hF hG K hK hpre R (min δg δa) hR (lt_min hδg hδa)
  let W := max Ma 1*(B/2+1)
  let SF := S+W
  let CF := Cχ*SF+1
  have hW : 0<W := by dsimp only [W]; positivity
  have hSF : 0<SF := by dsimp only [SF]; positivity
  have hCF : 0<CF := by dsimp only [CF]; positivity
  let ε₀ := min ep (min ed (min δ δχ/(SF+1)))
  have hε₀ : 0<ε₀ := by dsimp only [ε₀]; positivity
  refine ⟨ε₀,M,D,C,SF,CF,hε₀,hM,hD,hC,hSF,hCF,?_⟩
  intro ε hε he u hu hKu
  obtain ⟨hp,Θ,hA,hB',hhistory,ht,hsmall,hpoint⟩ := hinput ε hε
    (he.trans_le (min_le_left _ _)) u hu hKu
  let x₀ := ε • u
  let gn := ε⁻¹ • G x₀
  let v := gn-Q u
  let AP := rfcPhysicalSearch base Θ
  let BP := rfcPhysicalCorrection base Θ
  let Hk := rfcFunctionRun T f G fullMemory r x₀ k
  let d := rfcFunctionDirection fullMemory Hk
  let α := rfcPhysicalLineScale base (gn,Θ)
  let c : Fin (k+1) → ℝ := Fin.cons α (fun _=>1)
  let Δ := rfcFNormalizedRawValueChange T f G r x₀ k ε c
  have hgn : Q u+v=gn := by dsimp only [v]; abel
  have hscaleG : G x₀=ε • gn := by dsimp only [gn]; rw [smul_smul,mul_inv_cancel₀ hε.ne',one_smul]
  have ha' := ha (Q u) hKu v Θ (hsmall.trans (min_le_right _ _))
  rw [hgn] at ha'
  have hα : α≠0 := ha'.1
  have hInv : |α⁻¹^2|≤Ma := ha'.2.1
  have hgateN := hgate (Q u) hKu v Θ (hsmall.trans (min_le_left _ _))
  rw [hgn] at hgateN
  have hgateA : rfcFunctionGate fullMemory Hk := by
    rw [show Hk=methodRun (rfcMethod fullMemory 1) AP BP (G x₀) k from hhistory k (by omega),hscaleG]
    exact (rfcFunctionGate_scalar AP BP gn ε hε.ne' k hk).mpr hgateN
  have hαphysical : lineLength Hk.gradient d (AP k d)=α := by
    change lineLength Hk.gradient (rfcFunctionDirection fullMemory Hk)
      (AP k (rfcFunctionDirection fullMemory Hk))=_
    rw [show Hk=methodRun (rfcMethod fullMemory 1) AP BP (G x₀) k from hhistory k (by omega)]
    change rfcPhysicalLineScale base (G x₀,Θ)=α
    rw [hscaleG,rfcPhysicalLineScale_scalar base gn Θ ε hε.ne']
  have hgrad : Hk.gradient=G (x₀+Hk.displacement) := rfcFunctionRun_gradient T f G fullMemory r x₀ k
  have hlocal : ‖T (x₀+Hk.displacement)‖<r/2 := hpoint k (by omega)
  have hline := rfcFunctionLine_operator T hT f G H hr hG₀ hHc₀ hLr hH hF hG fullMemory x₀ Hk hgrad hlocal
  have hactualA : averagedDerivative H (x₀+Hk.displacement)
      (rfcFunctionLineStep T f fullMemory r x₀ Hk)=AP k := (hA k le_rfl).symm
  rw [hactualA] at hline
  dsimp only at hline
  rw [hαphysical] at hline
  have hy : G (rfcFAnchor T f G r x₀ k)-G (rfcFunctionPoint T f G fullMemory r x₀ k)=α • AP k d := by
    change G (rfcFunctionLinePoint T f fullMemory r x₀ Hk)-G (x₀+Hk.displacement)=_
    rw [hline.2,←hgrad]
    change Hk.gradient+lineLength Hk.gradient d (AP k d) • AP k d-Hk.gradient=_
    rw [hαphysical]
    abel
  have hpost : G (rfcFAnchor T f G r x₀ k)=fullPostSearch 1 AP BP (G x₀) k := by
    rw [show rfcFAnchor T f G r x₀ k=rfcFunctionLinePoint T f fullMemory r x₀ Hk from rfl,hline.2]
    rw [show Hk=methodRun (rfcMethod fullMemory 1) AP BP (G x₀) k from hhistory k (by omega)]
    rfl
  have hstep := rfcFCorrectionStep_normalized_operator T f G r x₀ AP BP k
    (fun j hj=>hhistory j (by omega)) α hα hline.1 hy hpost hgateA ε hε.ne'
  have hentry i : |rfcFNormalizedValueDiagonal T f G r x₀ k ε i|≤(B/2+1)*ε := by
    have hd := hdiag ε hε (he.trans_le ((min_le_right _ _).trans (min_le_left _ _))) u hu hKu i
    have hb := hcoeff (Q u) hKu i
    calc
      _ ≤ |rfcFNormalizedValueDiagonal T f G r x₀ k ε i-
        ε/2*inner ℝ (D₃ (referenceStep Q (Q u) i.val) (referenceStep Q (Q u) i.val)) (referenceStep Q (Q u) i.val)|+
        |ε/2*inner ℝ (D₃ (referenceStep Q (Q u) i.val) (referenceStep Q (Q u) i.val)) (referenceStep Q (Q u) i.val)| := by
          simpa only [Real.norm_eq_abs] using norm_le_norm_sub_add
            (rfcFNormalizedValueDiagonal T f G r x₀ k ε i)
            (ε/2*inner ℝ (D₃ (referenceStep Q (Q u) i.val) (referenceStep Q (Q u) i.val)) (referenceStep Q (Q u) i.val))
      _ ≤ ε+(ε/2)*B := add_le_add (by simpa only [one_mul] using hd)
        (by rw [abs_mul,abs_of_nonneg (by positivity : 0≤ε/2)]; exact mul_le_mul_of_nonneg_left hb (by positivity))
      _ = _ := by ring
  have hinv i : |(c i)⁻¹^2|≤max Ma 1 := by
    refine Fin.cases ?_ (fun _=>?_) i
    · exact hInv.trans (le_max_left _ _)
    · simpa only [c,Fin.cons_succ,inv_one,one_pow,abs_one] using le_max_right Ma 1
  have hΔ : ‖Δ‖≤W*ε := by
    have hh := rfcFNormalizedRawValueChange_norm T f G r x₀ k ε c ((B/2+1)*ε) (max Ma 1)
      (by positivity) (by positivity) hentry hinv
    exact hh.trans_eq (by dsimp only [W]; ring)
  have hfull : ‖(v,(Θ,Δ))‖≤SF*ε := by
    have hv : ‖v‖≤S*ε := (norm_fst_le (v,Θ)).trans ht
    have hΘ : ‖Θ‖≤S*ε := (norm_snd_le (v,Θ)).trans ht
    rw [Prod.norm_def,Prod.norm_def,max_le_iff,max_le_iff]
    exact ⟨hv.trans (by dsimp only [SF]; nlinarith),hΘ.trans (by dsimp only [SF]; nlinarith),
      hΔ.trans (by dsimp only [SF]; nlinarith)⟩
  have hnear : ‖(v,(Θ,Δ))‖≤min δ δχ := by
    have hh := (lt_div_iff₀ (by positivity : 0<SF+1)).mp
      (he.trans_le ((min_le_right _ _).trans (min_le_right _ _)))
    exact hfull.trans (by nlinarith only [hh,hε])
  have hquery := hχ (Q u) hKu v Θ Δ (hnear.trans (min_le_right _ _))
  rw [hgn] at hquery
  have hnorm : ‖rfcFCorrectionStep T f G r x₀ k‖≤CF*ε^2 := by
    rw [hstep,norm_smul,Real.norm_of_nonneg hε.le]
    exact (mul_le_mul_of_nonneg_left
      (hquery.trans (mul_le_mul_of_nonneg_left hfull hCχ)) hε.le).trans (by dsimp only [CF]; nlinarith)
  exact ⟨hp,Θ,hA,hB',hhistory,hα,hgateA,hfull,hnear.trans (min_le_left _ _),hstep,hnorm⟩

end
end krylov.Functions
