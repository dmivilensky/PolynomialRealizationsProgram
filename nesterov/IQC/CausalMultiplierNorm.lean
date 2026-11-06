import nesterov.IQC.CausalFourier

/-! The source homotopy gain depends only on the multiplier's uniform norm. -/
namespace nesterov.IQC
noncomputable section
open Set MeasureTheory polyak.General.IQC polyak.General.IQC.Fourier
open scoped BigOperators ENNReal
local instance : Fact (0<2*Real.pi):=⟨Real.two_pi_pos⟩

theorem multiply_norm_le (P : Coefficient circleMeasure ℂ) : ‖multiply P‖≤‖P‖ := by
  let A : (ℂ→L[ℝ]ℂ)→L[ℝ]ℂ→L[ℝ]ℂ:=(ContinuousLinearMap.apply ℝ ℂ).flip
  have hA : ‖A‖≤1 := by
    apply A.opNorm_le_bound₂ (by norm_num)
    intro T x
    change ‖T x‖≤1*‖T‖*‖x‖
    simpa only [one_mul] using T.le_opNorm x
  apply (multiply P).opNorm_le_bound (norm_nonneg P)
  intro f
  have hh:=ContinuousLinearMap.norm_holder_apply_apply_le A P f (r:=2)
  exact hh.trans (mul_le_mul_of_nonneg_right
    (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hA (norm_nonneg P)) (norm_nonneg f))

theorem scalarOperator_norm_le (p : Lp ℂ ∞ circleMeasure) : ‖scalarOperator p‖≤‖p‖ := by
  have hh:=(ContinuousLinearMap.lsmul ℝ ℂ : ℂ→L[ℝ](ℂ→L[ℝ]ℂ)).norm_compLp_le p
  simpa only [scalarOperator,ContinuousLinearMap.opNorm_lsmul,one_mul] using hh

private theorem blockForm_norm_le
    (P : Coefficient circleMeasure ℂ)
    (i j : (SequenceSpace ℂ×SequenceSpace ℂ)→L[ℝ]SequenceSpace ℂ)
    (hi : ∀ x,‖i x‖≤‖x‖) (hj : ∀ x,‖j x‖≤‖x‖) :
    ‖blockForm halfLineTransform P i j‖≤‖P‖ := by
  apply (blockForm halfLineTransform P i j).opNorm_le_bound₂ (norm_nonneg P)
  intro x y
  change ‖inner ℝ (halfLineTransform (i x)) (multiply P (halfLineTransform (j y)))‖≤_
  have hm : ‖multiply P (halfLineTransform (j y))‖≤‖P‖*‖j y‖ := by
    have hh:=(multiply P).le_opNorm (halfLineTransform (j y))
    rw [halfLineTransform.norm_map] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right (multiply_norm_le P) (norm_nonneg _))
  calc
    _≤‖halfLineTransform (i x)‖*‖multiply P (halfLineTransform (j y))‖:=norm_inner_le_norm _ _
    _≤‖i x‖*(‖P‖*‖j y‖):=by rw [halfLineTransform.norm_map];gcongr
    _≤‖x‖*(‖P‖*‖y‖):=by gcongr;exact hi x;exact hj y
    _=_:=by ring

/-- Every scalar block is bounded by the same matrix multiplier bound;
the resulting time-domain norm has no spatial-dimension factor. -/
theorem scalar_bilinearIQC_norm_le (P : Fin 2→Fin 2→Lp ℂ ∞ circleMeasure)
    {M : ℝ} (hP : ∀ i j,‖P i j‖≤M) :
    ‖bilinearIQC halfLineTransform (scalarIQC P)‖≤4*M := by
  let _ : NormedSpace ℝ ((SequenceSpace ℂ×SequenceSpace ℂ)→L[ℝ]ℝ):=inferInstance
  let _ : SeminormedAddCommGroup ((SequenceSpace ℂ×SequenceSpace ℂ)→L[ℝ]ℝ):=inferInstance
  have hblock (i j : (SequenceSpace ℂ×SequenceSpace ℂ)→L[ℝ] SequenceSpace ℂ)
      (hi : ∀ x,‖i x‖≤‖x‖) (hj : ∀ x,‖j x‖≤‖x‖) (a b : Fin 2) :
      ‖blockForm halfLineTransform (scalarOperator (P a b)) i j‖≤M :=
    (blockForm_norm_le _ _ _ hi hj).trans ((scalarOperator_norm_le _).trans (hP a b))
  have hf : ∀ x : SequenceSpace ℂ×SequenceSpace ℂ,‖x.1‖≤‖x‖:=fun _=>le_max_left _ _
  have hs : ∀ x : SequenceSpace ℂ×SequenceSpace ℂ,‖x.2‖≤‖x‖:=fun _=>le_max_right _ _
  have h00:=hblock (ContinuousLinearMap.fst ℝ _ _) (ContinuousLinearMap.fst ℝ _ _) hf hf 0 0
  have h01:=hblock (ContinuousLinearMap.fst ℝ _ _) (ContinuousLinearMap.snd ℝ _ _) hf hs 0 1
  have h10:=hblock (ContinuousLinearMap.snd ℝ _ _) (ContinuousLinearMap.fst ℝ _ _) hs hf 1 0
  have h11:=hblock (ContinuousLinearMap.snd ℝ _ _) (ContinuousLinearMap.snd ℝ _ _) hs hs 1 1
  let b00:=blockForm halfLineTransform (scalarOperator (P 0 0)) (ContinuousLinearMap.fst ℝ _ _) (ContinuousLinearMap.fst ℝ _ _)
  let b01:=blockForm halfLineTransform (scalarOperator (P 0 1)) (ContinuousLinearMap.fst ℝ _ _) (ContinuousLinearMap.snd ℝ _ _)
  let b10:=blockForm halfLineTransform (scalarOperator (P 1 0)) (ContinuousLinearMap.snd ℝ _ _) (ContinuousLinearMap.fst ℝ _ _)
  let b11:=blockForm halfLineTransform (scalarOperator (P 1 1)) (ContinuousLinearMap.snd ℝ _ _) (ContinuousLinearMap.snd ℝ _ _)
  change ‖((b00+b01)+b10)+b11‖≤4*M
  have h1:=norm_add_le b00 b01
  have h2:=norm_add_le (b00+b01) b10
  have h3:=norm_add_le ((b00+b01)+b10) b11
  linarith


namespace CausalFeedback

/-- The same explicit gain depends only on the scalar plant, the uniform
matrix coefficient bound and the strict gap. -/
theorem frequency_uniform_bound_of_norm_bound {d : ℕ}
    (F : CausalFeedback (EuclideanSpace ℝ (Fin d))) {h : ℕ→ℝ}
    (hh : Summable (fun n=>|h n|)) (hF : ∀ x,F.plant x=convolution h x)
    (P : Fin 2→Fin 2→Lp ℂ ∞ circleMeasure) {M ε : ℝ}
    (hP : ∀ i j,‖P i j‖≤M) (hε : 0<ε)
    (hgap : ∀ᵐ ω ∂circleMeasure,
      matrixGraphValue (P 0 0 ω) (P 0 1 ω) (P 1 0 ω) (P 1 1 ω) (transfer h ω)≤ -ε)
    (hpos : ∀ τ : ℝ,τ∈Icc (0:ℝ) 1→∀ x : SequenceSpace (EuclideanSpace ℝ (Fin d)),
      0≤∑ i : Fin d,∫ ω,pointValue (scalarIQC P) ω
        (halfLineTransform (coordinateSignal i x) ω)
        (halfLineTransform (coordinateSignal i (τ • F.deltaL2 x)) ω) ∂circleMeasure)
    {τ : ℝ} (hτ : τ∈Icc (0:ℝ) 1) (f : ℕ→EuclideanSpace ℝ (Fin d)) (hf : SquareSummable f) :
    SquareSummable (F.run τ f) ∧
      sequenceNorm (F.run τ f)≤aprioriConstant (8*M) F.gain ε*sequenceNorm f := by
  have hb : 2*‖bilinearIQC halfLineTransform (scalarIQC P)‖≤8*M:=by
    have hh:=scalar_bilinearIQC_norm_le P hP
    linarith
  have hm : 0≤M:=(norm_nonneg (P 0 0)).trans (hP 0 0)
  have hc : frequencyConstant P F.gain ε≤aprioriConstant (8*M) F.gain ε := by
    unfold frequencyConstant aprioriConstant
    gcongr
    exact F.gain_nonneg
  obtain ⟨hs,hn⟩:=F.frequency_uniform_bound hh hF P hε hgap hpos hτ f hf
  exact ⟨hs,hn.trans (mul_le_mul_of_nonneg_right hc (sequenceNorm_nonneg f))⟩

end CausalFeedback
end
end nesterov.IQC
