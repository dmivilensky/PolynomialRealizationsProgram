import krylov.Functions.NativeRFCFRawValueJets
import krylov.Functions.NativeRFCTensorComparison

/-!
Article: main_krylov, prop:Fcycle(i), full true-tensor model substitution.
Use: replace every actual search/correction average and the true observed
value-model change by their original third-derivative jets together.
Source: actual native prefix, genuine value-model source bound, exact finite
symmetric charts and compact bounded bilinearity of the modified response.
-/
namespace krylov.Functions
noncomputable section
open Set Metric Matrix krylov.Methods krylov.Reference krylov.Nonlinear krylov.Correction
open scoped InnerProductSpace NNReal Matrix.Norms.L2Operator
variable {k : ℕ}

/-- The genuine physical RFC-F cubic tensor coefficient, including the actual reference value-model diagonal.
Article: main_krylov, prop:Fcycle(i), before canonical orthonormal coordinates. -/
def rfcFTensorPhysicalCoefficient (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ)
    (D : EuclideanSpace ℝ (Fin (k+1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1)))
    (u : EuclideanSpace ℝ (Fin (k+1))) : EuclideanSpace ℝ (Fin (k+1)) :=
  rfcModifiedQuadratic base (cgOperator base u)
    (rfcTensorSearch (cgOperator base) D u) (rfcTensorCorrection (cgOperator base) D u)
    (rfcFReferenceRawValueChange base D u)

/-- Joint actual operator and model jets enter the genuine modified response with one additional source-scale factor.
Article: main_krylov, prop:Fcycle(i), finite genuine source substitution. -/
theorem rfcModifiedQuadratic_operator_jet_bound
    (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ)
    (hQ : (cgOperator base).toLinearMap.IsSymmetric)
    (g : EuclideanSpace ℝ (Fin (k+1)))
    (A B A' B' : ℕ → EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1)))
    (hA : ∀ j<k+1, (A j).toLinearMap.IsSymmetric) (hB : ∀ j<k+1, (B j).toLinearMap.IsSymmetric)
    (hA' : ∀ j<k+1, (A' j).toLinearMap.IsSymmetric) (hB' : ∀ j<k+1, (B' j).toLinearMap.IsSymmetric)
    (Δ Δ' : Matrix (Fin (k+1)) (Fin (k+1)) ℝ)
    (ε Ds W J M : ℝ) (hε : 0<ε) (hDs : 0≤Ds) (hW : 0≤W) (hJ : 0≤J) (hM : 0≤M)
    (hAb : ∀ j<k+1, ‖A j-cgOperator base‖≤Ds*ε)
    (hBb : ∀ j<k+1, ‖B j-cgOperator base‖≤Ds*ε)
    (hΔ : ‖Δ‖≤Ds*ε)
    (hAw : ∀ j<k+1, ‖A' j-cgOperator base‖≤W)
    (hBw : ∀ j<k+1, ‖B' j-cgOperator base‖≤W)
    (hΔ' : ‖Δ'‖≤W)
    (hAj : ∀ j<k+1, ‖(A j-cgOperator base)-ε • (A' j-cgOperator base)‖≤J)
    (hBj : ∀ j<k+1, ‖(B j-cgOperator base)-ε • (B' j-cgOperator base)‖≤J)
    (hΔj : ‖Δ-ε • Δ'‖≤J)
    (hresponse : ∀ Θ Ξ : RFCModifiedData k,
      ‖rfcModifiedQuadratic base g (rfcPhysicalSearch base Θ.1) (rfcPhysicalCorrection base Θ.1) Θ.2-
        rfcModifiedQuadratic base g (rfcPhysicalSearch base Ξ.1) (rfcPhysicalCorrection base Ξ.1) Ξ.2‖≤
        M*(‖Θ‖+‖Ξ‖)*‖Θ-Ξ‖) :
    ‖rfcModifiedQuadratic base g A B Δ-ε^2 • rfcModifiedQuadratic base g A' B' Δ'‖≤M*(Ds+W)*ε*J := by
  let Θ : RFCModifiedData k := (rfcPhysicalDataOfOperators base hQ A B hA hB,Δ)
  let Ω : RFCModifiedData k := (rfcPhysicalDataOfOperators base hQ A' B' hA' hB',Δ')
  have hΘ : ‖Θ‖≤Ds*ε := max_le (rfcPhysicalDataOfOperators_norm base hQ A B hA hB (Ds*ε)
    (by positivity) hAb hBb) hΔ
  have hΩ : ‖Ω‖≤W := max_le (rfcPhysicalDataOfOperators_norm base hQ A' B' hA' hB' W hW hAw hBw) hΔ'
  have hdiff : ‖Θ-ε • Ω‖≤J := max_le (rfcPhysicalDataOfOperators_jet_norm base hQ A B A' B'
    hA hB hA' hB' ε J hJ hAj hBj) hΔj
  have hc (X Y : ℕ → EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1)))
      (hX : ∀ j<k+1, (X j).toLinearMap.IsSymmetric) (hY : ∀ j<k+1, (Y j).toLinearMap.IsSymmetric)
      (D : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) :
      rfcModifiedQuadratic base g (rfcPhysicalSearch base (rfcPhysicalDataOfOperators base hQ X Y hX hY))
        (rfcPhysicalCorrection base (rfcPhysicalDataOfOperators base hQ X Y hX hY)) D=rfcModifiedQuadratic base g X Y D := by
    exact rfcModifiedQuadratic_congr_prefix base g _ _ X Y D
      (fun j hj=>rfcPhysicalDataOfOperators_search base hQ X Y hX hY j (by omega))
      (rfcPhysicalDataOfOperators_correction base hQ X Y hX hY k (by omega))
  have hh := hresponse Θ (ε • Ω)
  change ‖rfcModifiedQuadratic base g (rfcPhysicalSearch base Θ.1) (rfcPhysicalCorrection base Θ.1) Θ.2-
    rfcModifiedQuadratic base g (rfcPhysicalSearch base (ε • Ω.1)) (rfcPhysicalCorrection base (ε • Ω.1)) (ε • Ω.2)‖≤_ at hh
  rw [rfcModifiedQuadratic_source_smul] at hh
  change ‖rfcModifiedQuadratic base g (rfcPhysicalSearch base _) (rfcPhysicalCorrection base _) Δ-
    ε^2 • rfcModifiedQuadratic base g (rfcPhysicalSearch base _) (rfcPhysicalCorrection base _) Δ'‖≤_ at hh
  rw [hc A B hA hB,hc A' B' hA' hB'] at hh
  have hΩε : ‖ε • Ω‖≤ε*W := by
    rw [norm_smul,Real.norm_of_nonneg hε.le]
    exact mul_le_mul_of_nonneg_left hΩ hε.le
  exact hh.trans ((mul_le_mul
    (mul_le_mul_of_nonneg_left (add_le_add hΘ hΩε) hM) hdiff (norm_nonneg _) (by positivity)).trans_eq (by ring))

/-- The true reference raw value-model diagonal is uniformly bounded on every compact nondegenerate genuine CG reference.
Article: main_krylov, prop:Fcycle(i), reference-source boundedness. -/
theorem compact_rfcFReferenceRawValueChange_norm
    (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (D : EuclideanSpace ℝ (Fin (k+1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1)))
    (K : Set (EuclideanSpace ℝ (Fin (k+1)))) (hK : IsCompact K)
    (hpre : ∀ g∈K, ∀ i≤k, CG.gradient (cgOperator base) g i≠0) :
    ∃ W : ℝ, 0<W ∧ ∀ u : EuclideanSpace ℝ (Fin (k+1)), cgOperator base u∈K →
      ‖rfcFReferenceRawValueChange base D u‖≤W := by
  obtain ⟨hQ,hpos⟩ := cgOperator_positive base hb
  obtain ⟨B,hB,hcoeff⟩ := compact_reference_cubic_bound (cgOperator base) hQ hpos D k K hK
    (fun g hg i hi=>hpre g hg i (by omega))
  obtain ⟨δ,Ca,Ma,hδ,_,hMa,ha⟩ := compact_rfc_line_inverse_square base hb K hK hpre
  refine ⟨max Ma 1*(B/2),by positivity,?_⟩
  intro u hKu
  have hi := (ha (cgOperator base u) hKu 0 0 (by simpa using hδ.le)).2.1
  rw [add_zero,rfcPhysicalLineScale_reference base hb] at hi
  apply diagonal_scalar_product_norm _ _ (B/2) (max Ma 1) (by positivity) (by positivity)
  · intro i
    rw [abs_mul,abs_of_nonneg (by norm_num : (0:ℝ)≤1/2)]
    exact (mul_le_mul_of_nonneg_left (hcoeff _ hKu i.rev) (by norm_num : (0:ℝ)≤1/2)).trans_eq (by ring)
  · intro i
    refine Fin.cases ?_ (fun j=>?_) i
    · exact hi.trans (le_max_left _ _)
    · simp only [Fin.cons_succ,inv_one,one_pow,abs_one]
      exact le_max_right _ _

/-- Every true actual RFC-F operator/model jet admits a compact-uniform physical coefficient substitution, derived from the original function.
Article: main_krylov, prop:Fcycle(i), complete joint tensor substitution. -/
theorem nativeRFCF_tensor_comparison
    (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
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
    ∃ ε₀ C : ℝ, 0<ε₀ ∧ 0≤C ∧ ∀ ε : ℝ, 0<ε → ε<ε₀ →
      ∀ u : EuclideanSpace ℝ (Fin (k+1)), ‖u‖≤R → cgOperator base u∈K →
      ∀ J : ℝ, 0≤J →
      (∀ j<k+1,
        ‖rfcFunctionSearchOperator T f G H fullMemory r (ε • u) j-cgOperator base-
          ε • D (rfcReferenceSearchMidpoint (cgOperator base) u j)‖≤J ∧
        ‖rfcFunctionCorrectionOperator T f G H fullMemory r (ε • u) j-cgOperator base-
          ε • D (fcQuadraticReferencePoint (cgOperator base) u (j+1))‖≤J) →
      let α := rfcFActualLineScale T f G H r (ε • u) k
      let Δ := rfcFNormalizedRawValueChange T f G r (ε • u) k ε (Fin.cons α (fun _=>1))
      ‖Δ-ε • rfcFReferenceRawValueChange base D u‖≤J →
      ‖rfcModifiedQuadratic base (cgOperator base u)
          (rfcFunctionSearchOperator T f G H fullMemory r (ε • u))
          (rfcFunctionCorrectionOperator T f G H fullMemory r (ε • u)) Δ-
        ε^2 • rfcFTensorPhysicalCoefficient base D u‖≤C*ε*J := by
  let Q := cgOperator base
  obtain ⟨hQ,hpos⟩ := cgOperator_positive base hb
  have hpref : ∀ g∈K, ∀ i<k+1, CG.gradient Q g i≠0 := fun g hg i hi=>hpre g hg i (by omega)
  obtain ⟨ep,M,Ds,Cp,hep,hM,hDs,_,hprefix⟩ := nativeRFC_compact_prefix T hT f G H Q hr hG₀ hH₀ hHc₀
    hLr hH hF hG hQ hpos (k+1) K hK hpref R hR
  obtain ⟨ej,hej,hjets⟩ := nativeRFC_reference_operator_jets T hT f G H Q D hD hr hG₀ hH₀ hHc₀
    hLr hH hF hG hQ hpos (k+1) K hK hpref R hR 1 zero_lt_one
  obtain ⟨ev,hev,hvalue⟩ := nativeRFCF_raw_value_jet base hb T hT f G H D hD hr hG₀ hH₀ hHc₀
    hLr hH hF hG K hK hpre R hR 1 zero_lt_one
  obtain ⟨W,hW,hWbound⟩ := compact_rfcFReferenceRawValueChange_norm base hb D K hK hpre
  obtain ⟨Mb,hMb,hresponse⟩ := compact_rfcModifiedQuadratic_difference base hb K hK hpre
  let e := min ep ej/2
  have he : 0<e := by dsimp only [e]; positivity
  have heep : e<ep := by have hh := min_le_left ep ej; dsimp only [e]; linarith only [hh,hep]
  have heej : e<ej := by have hh := min_le_right ep ej; dsimp only [e]; linarith only [hh,hej]
  have hleading (u : EuclideanSpace ℝ (Fin (k+1))) (hu : ‖u‖≤R) (hKu : Q u∈K) (j : ℕ) (hj : j<k+1) :
      ‖D (rfcReferenceSearchMidpoint Q u j)‖≤Ds+1 ∧
      ‖D (fcQuadraticReferencePoint Q u (j+1))‖≤Ds+1 := by
    have hp := hprefix e he heep u hu hKu
    have hz := hjets e he heej u hu hKu j hj
    simp only [one_mul] at hz
    exact ⟨leading_norm_bound_of_jet _ _ e Ds he (hp.2 j hj).1 hz.1,
      leading_norm_bound_of_jet _ _ e Ds he (hp.2 j hj).2.1 hz.2⟩
  let Z := Ds+W+1
  have hZ : 0≤Z := by dsimp only [Z]; positivity
  let ε₀ := min ep (min ev (r/(‖T.toContinuousLinearMap‖*M+1)))
  have hε₀ : 0<ε₀ := by dsimp only [ε₀]; positivity
  refine ⟨ε₀,Mb*(Z+Z),hε₀,by positivity,?_⟩
  intro ε hε he' u hu hKu J hJ hjets'
  dsimp only
  intro hvalue'
  let α := rfcFActualLineScale T f G H r (ε • u) k
  let Δ := rfcFNormalizedRawValueChange T f G r (ε • u) k ε (Fin.cons α (fun _=>1))
  have hp := hprefix ε hε (he'.trans_le (min_le_left _ _)) u hu hKu
  have hv := hvalue ε hε (he'.trans_le ((min_le_right _ _).trans (min_le_left _ _))) u hu hKu
  have hΔ : ‖Δ‖≤Z*ε := by
    have hn := norm_le_norm_sub_add Δ (ε • rfcFReferenceRawValueChange base D u)
    have hn' : ‖ε • rfcFReferenceRawValueChange base D u‖≤ε*W := by
      rw [norm_smul,Real.norm_of_nonneg hε.le]
      exact mul_le_mul_of_nonneg_left (hWbound u hKu) hε.le
    simp only [one_mul] at hv
    exact (hn.trans (add_le_add hv hn')).trans (by dsimp only [Z]; nlinarith only [hDs,hε])
  have hscale : ‖T.toContinuousLinearMap‖*(M*ε)<r := by
    have hh := (lt_div_iff₀ (by positivity : 0<‖T.toContinuousLinearMap‖*M+1)).mp
      (he'.trans_le ((min_le_right _ _).trans (min_le_right _ _)))
    nlinarith only [hh,hε]
  have hsym := hp.operator_symmetric T f G H Q r u ε M Ds Cp (k+1) hscale hH hF hG
  have hs (v : EuclideanSpace ℝ (Fin (k+1))) := genuine_third_slice_symmetric T f G H D hD hr hF hG v
  have hAs j (_hj : j<k+1) : (rfcTensorSearch Q D u j).toLinearMap.IsSymmetric := hQ.add (hs _)
  have hBs j (_hj : j<k+1) : (rfcTensorCorrection Q D u j).toLinearMap.IsSymmetric := hQ.add (hs _)
  have hAn j (hj : j<k+1) : ‖rfcTensorSearch Q D u j-Q‖≤Z := by
    have hh := (hleading u hu hKu j hj).1
    simpa only [rfcTensorSearch,add_sub_cancel_left] using hh.trans (by dsimp only [Z]; linarith only [hW])
  have hBn j (hj : j<k+1) : ‖rfcTensorCorrection Q D u j-Q‖≤Z := by
    have hh := (hleading u hu hKu j hj).2
    simpa only [rfcTensorCorrection,add_sub_cancel_left] using hh.trans (by dsimp only [Z]; linarith only [hW])
  exact rfcModifiedQuadratic_operator_jet_bound base hQ (Q u) _ _
    (rfcTensorSearch Q D u) (rfcTensorCorrection Q D u)
    (fun j hj=>(hsym j hj).1) (fun j hj=>(hsym j hj).2) hAs hBs Δ (rfcFReferenceRawValueChange base D u)
    ε Z Z J Mb hε hZ hZ hJ hMb
    (fun j hj=>(hp.2 j hj).1.trans (mul_le_mul_of_nonneg_right (by dsimp only [Z]; linarith only [hW]) hε.le))
    (fun j hj=>(hp.2 j hj).2.1.trans (mul_le_mul_of_nonneg_right (by dsimp only [Z]; linarith only [hW]) hε.le))
    hΔ hAn hBn ((hWbound u hKu).trans (by dsimp only [Z]; linarith only [hDs]))
    (fun j hj=>by simpa only [rfcTensorSearch,Q,add_sub_cancel_left] using (hjets' j hj).1)
    (fun j hj=>by simpa only [rfcTensorCorrection,Q,add_sub_cancel_left] using (hjets' j hj).2)
    hvalue' (hresponse (Q u) hKu)

end
end krylov.Functions
