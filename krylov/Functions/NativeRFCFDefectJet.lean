import krylov.Functions.NativeRFCFReference
import krylov.Functions.NativeRFCJets
import krylov.Functions.ValueDefectReferenceJet

/-!
Article: main_krylov, prop:Fcycle(i), actual RFC-F retained value defects.
Use: prove every true observed pair has the printed cubic value-defect jet,
uniformly over the original compact nondegenerate quadratic references.
All pair locations and small steps are derived from the genuine unchanged
ordinary-RFC prefix. Source: native compact bootstrap, true segment/reference
shadows, and the independently proved second-derivative trapezoid kernel.
-/

namespace krylov.Functions
noncomputable section
open Real Set Metric Filter Topology krylov.Methods krylov.Reference krylov.Nonlinear chebyshev1.Nonlinear
open scoped InnerProductSpace NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The leading reference step is bounded by its actual linear step bound and genuine quadratic shadow.
Article: main_krylov, prop:Fcycle(i), uniform native normalization. -/
theorem referenceStep_bound_of_shadow (s σ : E) (ε A C : ℝ)
    (hε : 0 < ε) (he : ε ≤ 1) (hC : 0 ≤ C)
    (hs : ‖s‖ ≤ A * ε) (herr : ‖s - ε • σ‖ ≤ C * ε ^ 2) :
    ‖σ‖ ≤ A + C := by
  have hn := norm_sub_le s (s - ε • σ)
  rw [sub_sub_cancel, norm_smul, Real.norm_of_nonneg hε.le] at hn
  have hε2 : ε ^ 2 ≤ ε := by nlinarith only [hε, he]
  have hh := mul_le_mul_of_nonneg_left hε2 hC
  nlinarith only [hn, hs, herr, hh, hε]

variable [CompleteSpace E] [FiniteDimensional ℝ E]

/-- Every actual scalar value defect retained by native RFC-F has its genuine third-derivative first jet.
Article: main_krylov, prop:Fcycle(i), the physical unnormalized defect formula.
The original physical Hessian derivative at zero suffices for the uniform
little-o remainder; no prescribed model or observed-defect expansion is an input. -/
theorem nativeRFCF_value_defect_jet (T : E ≃L[ℝ] E)
    (hT : T.symm.toContinuousLinearMap.IsSymmetric)
    (f : E → ℝ) (G : E → E) (H : E → E →L[ℝ] E) (Q : E →L[ℝ] E)
    (D : E →L[ℝ] E →L[ℝ] E) (hD : HasFDerivAt H D 0)
    {r : ℝ} (hr : 0 < r) (hG₀ : G 0 = 0) (hH₀ : H 0 = Q)
    (hHc₀ : coordinateDerivative T H 0 = ContinuousLinearMap.id ℝ E)
    {L : NNReal} (hLr : (L : ℝ) * r ≤ 1 / 2)
    (hH : LipschitzOnWith L (coordinateDerivative T H) (closedBall 0 r))
    (hF : ∀ z : E, ‖T z‖ ≤ r → HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z : E, ‖T z‖ ≤ r → HasFDerivAt G (H z) z)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E, v ≠ 0 → 0 < inner ℝ v (Q v))
    (k : ℕ) (K : Set E) (hK : IsCompact K)
    (hpre : ∀ g ∈ K, ∀ i < k + 1, CG.gradient Q g i ≠ 0)
    (R : ℝ) (hR : 0 < R) :
    ∀ η : ℝ, 0 < η → ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∀ u : E, ‖u‖ ≤ R → Q u ∈ K → ∀ i : Fin (k+1),
      |segmentValueDefect f (fun x => innerSL ℝ (G x))
          (rfcFAnchors T f G r (ε • u) k i) (rfcFSteps T f G r (ε • u) k i) +
        ε ^ 3 * inner ℝ (D (referenceStep Q (Q u) i.val) (referenceStep Q (Q u) i.val))
          (referenceStep Q (Q u) i.val) / 12| ≤ η * ε ^ 3 := by
  obtain ⟨ep, M, Da, C, hep, hM, _, hC, hprefix⟩ := nativeRFC_compact_prefix T hT f G H Q
    hr hG₀ hH₀ hHc₀ hLr hH hF hG hQ hpos (k+1) K hK hpre R hR
  let rp := r / (‖T.toContinuousLinearMap‖ + 1)
  have hrp : 0 < rp := by dsimp only [rp]; positivity
  have hball : ball (0 : E) rp ⊆ T ⁻¹' closedBall (0 : E) r := by
    intro z hz
    rw [mem_preimage, mem_closedBall, dist_zero_right]
    have hz' : ‖z‖ ≤ rp := (by simpa only [mem_ball, dist_zero_right] using hz : ‖z‖ < rp).le
    have hb := (T.toContinuousLinearMap.le_opNorm z).trans
      (mul_le_mul_of_nonneg_left hz' (norm_nonneg _))
    have ht : ‖T.toContinuousLinearMap‖ * rp ≤ r := by
      dsimp only [rp]
      rw [← mul_div_assoc]
      apply (div_le_iff₀ (by positivity : 0 < ‖T.toContinuousLinearMap‖ + 1)).mpr
      nlinarith only [hr]
    exact hb.trans ht
  have hc : ContinuousOn H (ball 0 rp) :=
    (coordinateDerivative_lipschitz_pullback T H hH).continuousOn.mono hball
  have hF' z (hz : z ∈ ball (0 : E) rp) := hF z
    (by simpa only [mem_preimage, mem_closedBall, dist_zero_right] using hball hz)
  have hG' z (hz : z ∈ ball (0 : E) rp) := hG z
    (by simpa only [mem_preimage, mem_closedBall, dist_zero_right] using hball hz)
  let Cs := (2 * (k : ℝ) + 2) * C
  have hCs : 0 ≤ Cs := by dsimp only [Cs]; positivity
  let Mb := 2 * M + Cs + 1
  have hMb : 0 < Mb := by dsimp only [Mb]; positivity
  intro η hη
  obtain ⟨ej, hej, hj⟩ := segmentValueDefect_reference_jet f G H D hrp hD hc hF' hG'
    Mb Cs hMb hCs η hη
  refine ⟨min ep (min ej 1), lt_min hep (lt_min hej (by norm_num)), ?_⟩
  intro ε hε he u hu hKu i
  have hp := hprefix ε hε (he.trans_le (min_le_left _ _)) u hu hKu
  have hs := hp.rfcF_steps_local T f G H Q r u ε M Da C k i
  have herr := hp.rfcF_reference_steps T f G H Q r u ε M Da C k hC.le i
  change ‖rfcFSteps T f G r (ε • u) k i - ε • referenceStep Q (Q u) i.val‖ ≤ Cs * ε ^ 2 at herr
  have hσ := referenceStep_bound_of_shadow _ _ ε (2 * M) Cs hε
    (he.trans_le ((min_le_right _ _).trans (min_le_right _ _))).le hCs hs herr
  have hle : 2 * M ≤ Mb := by dsimp only [Mb]; linarith only [hCs]
  have hle' : 2 * M + Cs ≤ Mb := by dsimp only [Mb]; linarith
  apply hj ε hε (he.trans_le ((min_le_right _ _).trans (min_le_left _ _)))
    (rfcFAnchors T f G r (ε • u) k i) (rfcFSteps T f G r (ε • u) k i)
    (referenceStep Q (Q u) i.val)
  · intro t ht
    have hends := hp.rfcF_segments_local T f G H Q r u ε M Da C k i
    have hseg := segment_norm_le_endpoints _ _ (M * ε) hends.1 hends.2 t ht
    rw [add_sub_cancel_left] at hseg
    exact hseg.trans (mul_le_mul_of_nonneg_right (by dsimp only [Mb]; linarith only [hM, hCs]) hε.le)
  · exact hs.trans (mul_le_mul_of_nonneg_right hle hε.le)
  · exact hσ.trans hle'
  · exact herr

end
end krylov.Functions
