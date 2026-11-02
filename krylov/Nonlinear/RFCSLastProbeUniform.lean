import krylov.Nonlinear.RFCSCanonicalMismatch
import krylov.Nonlinear.RFCSCycleGeometry
import krylov.Correction.RFCSCompactBounds

/-!
Article: main_krylov, thm:RFCS, actual uniform last-probe leading coefficient.
Use: Derive the genuine canonical last averaged-Hessian mismatch bound with
the literal executed relative probe error and a common quadratic remainder,
from original local gradient/Hessian data and actual canonical local control.
Source: the shared genuine nonlinear source, actual line/correction geometry,
exact canonical measured-average comparison and proved compact CG lengths.
-/

namespace krylov.Nonlinear
noncomputable section
open Set Metric krylov.Methods krylov.Reference krylov.Correction krylov.Stability
open scoped NNReal
variable {k : ℕ}

set_option maxHeartbeats 800000 in
/-- Genuine nonlinear RFC-S cycles under actual canonical Hessian control 2+10000R have last averaged-probe mismatch bounded by the executed relative probe error times the original reference last-step norm, with one uniform quadratic cycle remainder.
Use: Preserve the exact source leading coefficient when inserting the real last probe mismatch in the genuine nonlinear cubic output expansion.
Article: main_krylov, thm:RFCS, actual uniform nonlinear last-probe coefficient.
Proof: Compact true CG lengths turn the original relative probe restriction into a real bounded query family. The shared genuine nonlinear source encloses every true canonical query in a ball proportional to the actual cycle size. Actual search/correction geometry gives the real quadratic step errors and positive predicted length; the true relative probe error stays uniformly bounded. Apply the exact canonical averaged-Hessian mismatch theorem and expand only the higher-order products, keeping the actual leading probe factor unchanged.
-/
theorem compact_rfcs_coordinate_last_probe_bound (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (K : Set (EuclideanSpace ℝ (Fin (k+1)))) (hK : IsCompact K)
    (hN : ∀ g∈K, k+1≤referenceAtomCount base hb g)
    (T : EuclideanSpace ℝ (Fin (k+1)) ≃L[ℝ] EuclideanSpace ℝ (Fin (k+1)))
    (G : EuclideanSpace ℝ (Fin (k+1)) → EuclideanSpace ℝ (Fin (k+1)))
    (H : EuclideanSpace ℝ (Fin (k+1)) → EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1)))
    (r B Cp ρ : ℝ) (hr : 0<r) (hB : 0<B) (hCp : 0<Cp) (hρ : 0<ρ)
    (hG₀ : G 0=0) (hH₀ : H 0=cgOperator base) {L : ℝ≥0}
    (hH : LipschitzOnWith L H (ball 0 r)) (hG : ∀ x∈ball 0 r, HasFDerivAt G (H x) x)
    (hcan : ∀ R : ℝ, 0<R → R≤ρ → LipschitzOnWith (Real.toNNReal (2+10000*R)) (coordinateDerivative T H) (ball 0 R)) :
    ∃ ε₀ C : ℝ, 0<ε₀ ∧ 0<C ∧ ∀ ε : ℝ, 0<ε → ε<ε₀ →
      ∀ u : EuclideanSpace ℝ (Fin (k+1)), ‖u‖≤B → cgOperator base u∈K →
      ∀ h : ℕ → ℝ, (∀ i, h i≠0) →
      (∀ i<k+1, 0<h i ∧ h i≤Cp*CG.length (cgOperator base) (cgOperator base u) i) →
      ‖coordinateCongruence T (rfcSFunctionSegment fullMemory G H (ε • u) h k-
        rfcSFunctionProbeOperator fullMemory G H (ε • u) h k)‖≤
      |1-h k/rfcSFunctionAlpha fullMemory G (ε • u) h k| *ε*
        ‖T (referenceStep (cgOperator base) (cgOperator base u) k)‖+C*ε^2 := by
  obtain ⟨Mα,hMα,hαref⟩ := compact_rfcs_reference_length_bounds base hb K hK hN
  let P := Cp*Mα
  have hP : 0≤P := (mul_pos hCp hMα).le
  obtain ⟨ε₁,D,_,hε₁,hD,_,hsource⟩ := compact_rfcs_nonlinear_source base hb K hK hN G H r B P hr hB hP hG₀ hH₀ hH hG
  obtain ⟨ε₂,Cg,hε₂,hCg,hgeo⟩ := compact_rfcs_nonlinear_search_geometry base hb K hK hN G H r B P hr hB hP hG₀ hH₀ hH hG
  obtain ⟨δ,M,hδ,hM,hprefix⟩ := compact_rfcs_operator_prefix_bounds base hb K hK hN
  have href g (hg : g∈K) : ‖referenceStep (cgOperator base) g k‖≤M := by
    have hh := ((hprefix g hg 0 0 (by simp only [Prod.norm_mk,norm_zero,max_self]; linarith)).2 k (Nat.lt_succ_self k)).2
    rw [add_zero] at hh
    have hzero := (rfcs_direct_alpha_reference base hb g k).2.2
    unfold rfcsDirectCorrection at hzero
    rw [(rfcs_direct_alpha_reference base hb g k).2.1] at hzero
    rw [sub_eq_zero.mp hzero] at hh
    exact hh
  let q := ‖T.toContinuousLinearMap‖*D+1
  have hq : 0<q := by dsimp only [q]; positivity
  let A := 5000*q
  let b := ‖T.toContinuousLinearMap‖*Cg
  let Emax := 1+2*Cp
  let Mref := (‖T.toContinuousLinearMap‖+1)*M+1
  have hA : 0≤A := by dsimp only [A]; positivity
  have hb' : 0≤b := by dsimp only [b]; positivity
  have hMref : 0<Mref := by dsimp only [Mref]; positivity
  have hEmax : 0<Emax := by dsimp only [Emax]; positivity
  let C := A*Emax*Mref+b*(Emax+1)*(1+A)+1
  have hC : 0<C := by dsimp only [C]; positivity
  refine ⟨min ε₁ (min ε₂ (min (ρ/(q+1)) 1)),C,
    lt_min hε₁ (lt_min hε₂ (lt_min (div_pos hρ (by positivity)) (by norm_num))),hC,?_⟩
  intro ε hε he u hu hKu h hh hrel
  have habs i (hi : i<k+1) : |h i|≤P := by
    rw [abs_of_pos (hrel i hi).1]
    exact (hrel i hi).2.trans (mul_le_mul_of_nonneg_left (hαref _ hKu i hi).2.2 hCp.le)
  have hs := hsource ε hε (he.trans_le (min_le_left _ _)) u hu hKu h hh habs
  have hg := hgeo ε hε (he.trans_le ((min_le_right _ _).trans (min_le_left _ _))) u hu hKu h hh habs k (Nat.lt_succ_self k)
  have hε1 : ε≤1 := he.le.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hRq : q*ε≤ρ := by
    have he' := (lt_div_iff₀ (by positivity : 0<q+1)).mp
      (he.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
    nlinarith
  have hmap (y : EuclideanSpace ℝ (Fin (k+1))) (hy : ‖y‖≤ε*D) : T y∈ball 0 (q*ε) := by
    rw [mem_ball_zero_iff]
    have hn := T.toContinuousLinearMap.le_opNorm y
    simp only [ContinuousLinearEquiv.coe_coe] at hn
    have hn' := mul_le_mul_of_nonneg_left hy (norm_nonneg T.toContinuousLinearMap)
    dsimp only [q]
    nlinarith
  have hLcan := hcan (q*ε) (mul_pos hq hε) hRq
  -- Use the true current, next and finite-probe endpoints; no hypothetical segment or trajectory is supplied.
  have hbound := rfcSFunction_canonical_mismatch_bound T fullMemory G H (ε • u) h k (convex_ball _ _) hLcan hg.1
    (hmap _ (hs.2.1 k (by omega)).2) (hmap _ (hs.2.1 (k+1) le_rfl).2) (hmap _ (hs.2.2 k (Nat.lt_succ_self k)))
  have hcoef : ((Real.toNNReal (2+10000*(q*ε)) : ℝ≥0) : ℝ)/2=1+A*ε := by
    rw [Real.coe_toNNReal _ (by positivity)]
    dsimp only [A]
    ring
  rw [hcoef] at hbound
  let E := |1-h k/rfcSFunctionAlpha fullMemory G (ε • u) h k|
  let e := ‖T (referenceStep (cgOperator base) (cgOperator base u) k)‖
  have hE : 0≤E := abs_nonneg _
  have hEbound : E≤Emax := relative_probe_error_bound (hαref _ hKu k (Nat.lt_succ_self k)).1
    hg.2.1 (hrel k (Nat.lt_succ_self k)).1 (hrel k (Nat.lt_succ_self k)).2
  have heRef : e≤Mref := by
    have hn := T.toContinuousLinearMap.le_opNorm (referenceStep (cgOperator base) (cgOperator base u) k)
    simp only [ContinuousLinearEquiv.coe_coe] at hn
    apply hn.trans
    apply (mul_le_mul_of_nonneg_left (href _ hKu) (norm_nonneg T.toContinuousLinearMap)).trans
    dsimp only [Mref]
    nlinarith
  have hlineError : ‖T (rfcSFunctionLineStep fullMemory G (ε • u) h k)-ε • T (referenceStep (cgOperator base) (cgOperator base u) k)‖≤b*ε^2 := by
    have hn := T.toContinuousLinearMap.le_opNorm (rfcSFunctionLineStep fullMemory G (ε • u) h k-
      ε • referenceStep (cgOperator base) (cgOperator base u) k)
    simp only [map_sub,map_smul,ContinuousLinearEquiv.coe_coe] at hn
    exact hn.trans ((mul_le_mul_of_nonneg_left hg.2.2.2.1 (norm_nonneg _)).trans_eq (by dsimp only [b]; ring))
  have hline : ‖T (rfcSFunctionLineStep fullMemory G (ε • u) h k)‖≤ε*e+b*ε^2 := by
    have hn := norm_add_le (T (rfcSFunctionLineStep fullMemory G (ε • u) h k)-
      ε • T (referenceStep (cgOperator base) (cgOperator base u) k))
      (ε • T (referenceStep (cgOperator base) (cgOperator base u) k))
    rw [sub_add_cancel,norm_smul,Real.norm_of_nonneg hε.le] at hn
    linarith
  have hcorr : ‖T (rfcSFunctionCorrection fullMemory G (ε • u) h k)‖≤b*ε^2 := by
    have hn := T.toContinuousLinearMap.le_opNorm (rfcSFunctionCorrection fullMemory G (ε • u) h k)
    simp only [ContinuousLinearEquiv.coe_coe] at hn
    exact hn.trans ((mul_le_mul_of_nonneg_left hg.2.2.2.2 (norm_nonneg _)).trans_eq (by dsimp only [b]; ring))
  have hresult := bounded_last_probe_product hE hEbound (norm_nonneg _) heRef hA hb' hε.le hε1 hbound hline hcorr
  apply hresult.trans
  dsimp only [C]
  nlinarith [sq_nonneg ε]

end
end krylov.Nonlinear
