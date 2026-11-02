import krylov.Functions.NativeRFCFDefectJet

/-!
Article: main_krylov, prop:Fcycle(i), the Lipschitz-third defect refinement.
Use: derive a uniform fourth-order remainder for every real value defect
retained by the actual native RFC-F last model. Source: genuine native query
enclosure, actual reference-step shadows and the second-kernel remainder.
-/

namespace krylov.Functions
noncomputable section
open Real Set Metric Filter Topology krylov.Methods krylov.Reference krylov.Nonlinear chebyshev1.Nonlinear
open scoped InnerProductSpace NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

/-- A genuine Lipschitz third derivative gives the actual RFC-F retained defects their uniform fourth-order remainder.
Article: main_krylov, prop:Fcycle(i), the physical cubic-defect refinement. -/
theorem nativeRFCF_value_defect_quartic (T : E ≃L[ℝ] E)
    (hT : T.symm.toContinuousLinearMap.IsSymmetric)
    (f : E → ℝ) (G : E → E) (H : E → E →L[ℝ] E) (Q : E →L[ℝ] E)
    (D : E → E →L[ℝ] E →L[ℝ] E)
    {r : ℝ} (hr : 0 < r) (hG₀ : G 0 = 0) (hH₀ : H 0 = Q)
    (hHc₀ : coordinateDerivative T H 0 = ContinuousLinearMap.id ℝ E)
    {L L₃ : NNReal} (hLr : (L : ℝ) * r ≤ 1 / 2)
    (hH : LipschitzOnWith L (coordinateDerivative T H) (closedBall 0 r))
    (hD : ∀ z : E, ‖T z‖ ≤ r → HasFDerivAt H (D z) z)
    (hDlip : LipschitzOnWith L₃ D (T ⁻¹' closedBall (0 : E) r))
    (hF : ∀ z : E, ‖T z‖ ≤ r → HasFDerivAt f (innerSL ℝ (G z)) z)
    (hG : ∀ z : E, ‖T z‖ ≤ r → HasFDerivAt G (H z) z)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E, v ≠ 0 → 0 < inner ℝ v (Q v))
    (k : ℕ) (K : Set E) (hK : IsCompact K)
    (hpre : ∀ g ∈ K, ∀ i < k + 1, CG.gradient Q g i ≠ 0)
    (R : ℝ) (hR : 0 < R) :
    ∃ ε₀ Cδ : ℝ, 0 < ε₀ ∧ 0 < Cδ ∧
      ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∀ u : E, ‖u‖ ≤ R → Q u ∈ K → ∀ i : Fin (k+1),
      |segmentValueDefect f (fun x => innerSL ℝ (G x))
          (rfcFAnchors T f G r (ε • u) k i) (rfcFSteps T f G r (ε • u) k i) +
        ε ^ 3 * inner ℝ (D 0 (referenceStep Q (Q u) i.val) (referenceStep Q (Q u) i.val))
          (referenceStep Q (Q u) i.val) / 12| ≤ Cδ * ε ^ 4 := by
  obtain ⟨ep, M, Da, C, hep, hM, _, hC, hprefix⟩ := nativeRFC_compact_prefix T hT f G H Q
    hr hG₀ hH₀ hHc₀ hLr hH hF hG hQ hpos (k+1) K hK hpre R hR
  let S := T ⁻¹' closedBall (0 : E) r
  have hS : Convex ℝ S := by
    intro a ha b hb p q hp hq hpq
    change T (p • a + q • b) ∈ closedBall (0 : E) r
    simpa only [map_add, map_smul] using (convex_closedBall (0 : E) r) ha hb hp hq hpq
  have hz : (0 : E) ∈ S := by simp [S, hr.le]
  have hd z (hz : z ∈ S) := hD z
    (by simpa only [S, mem_preimage, mem_closedBall, dist_zero_right] using hz)
  have hf z (hz : z ∈ S) := hF z
    (by simpa only [S, mem_preimage, mem_closedBall, dist_zero_right] using hz)
  have hg z (hz : z ∈ S) := hG z
    (by simpa only [S, mem_preimage, mem_closedBall, dist_zero_right] using hz)
  let Cs := (2 * (k : ℝ) + 2) * C
  have hCs : 0 ≤ Cs := by dsimp only [Cs]; positivity
  let Mb := 2 * M + Cs + 1
  have hMb : 0 < Mb := by dsimp only [Mb]; positivity
  let Cδ := (L₃ : ℝ) * Mb ^ 4 / 2 + ‖D 0‖ * Mb ^ 2 * Cs / 4 + 1
  have hCδ : 0 < Cδ := by dsimp only [Cδ]; positivity
  let ε₀ := min ep (min 1 (r / (‖T.toContinuousLinearMap‖ * M + 1)))
  have hε₀ : 0 < ε₀ := by dsimp only [ε₀]; positivity
  refine ⟨ε₀, Cδ, hε₀, hCδ, ?_⟩
  intro ε hε he u hu hKu i
  have hp := hprefix ε hε (he.trans_le (min_le_left _ _)) u hu hKu
  have hs := hp.rfcF_steps_local T f G H Q r u ε M Da C k i
  have herr := hp.rfcF_reference_steps T f G H Q r u ε M Da C k hC.le i
  change ‖rfcFSteps T f G r (ε • u) k i - ε • referenceStep Q (Q u) i.val‖ ≤ Cs * ε ^ 2 at herr
  have hσ := referenceStep_bound_of_shadow _ _ ε (2 * M) Cs hε
    (he.trans_le ((min_le_right _ _).trans (min_le_left _ _))).le hCs hs herr
  have hle : 2 * M ≤ Mb := by dsimp only [Mb]; linarith only [hCs]
  have hle' : 2 * M + Cs ≤ Mb := by dsimp only [Mb]; linarith
  have hseg t (ht : t ∈ Icc (0 : ℝ) 1) :
      rfcFAnchors T f G r (ε • u) k i + t • rfcFSteps T f G r (ε • u) k i ∈ S ∧
      ‖rfcFAnchors T f G r (ε • u) k i + t • rfcFSteps T f G r (ε • u) k i‖ ≤ Mb * ε := by
    have hends := hp.rfcF_segments_local T f G H Q r u ε M Da C k i
    have hb := segment_norm_le_endpoints _ _ (M * ε) hends.1 hends.2 t ht
    rw [add_sub_cancel_left] at hb
    refine ⟨?_, hb.trans (mul_le_mul_of_nonneg_right (by dsimp only [Mb]; linarith only [hM, hCs]) hε.le)⟩
    dsimp only [S]
    rw [mem_preimage, mem_closedBall, dist_zero_right]
    have hnorm := (T.toContinuousLinearMap.le_opNorm _).trans
      (mul_le_mul_of_nonneg_left hb (norm_nonneg _))
    change ‖T (rfcFAnchors T f G r (ε • u) k i + t • rfcFSteps T f G r (ε • u) k i)‖ ≤
      ‖T.toContinuousLinearMap‖ * (M * ε) at hnorm
    have he' := (lt_div_iff₀ (by positivity : 0 < ‖T.toContinuousLinearMap‖ * M + 1)).mp
      (he.trans_le ((min_le_right _ _).trans (min_le_right _ _)))
    nlinarith only [hnorm, he', hε]
  have hb := segmentValueDefect_reference_quartic f G H D S hS hz hf hg hd hDlip
    (rfcFAnchors T f G r (ε • u) k i) (rfcFSteps T f G r (ε • u) k i)
    (referenceStep Q (Q u) i.val) ε Mb Cs hε.le hMb.le hCs hseg
    (hs.trans (mul_le_mul_of_nonneg_right hle hε.le)) (hσ.trans hle') herr
  apply hb.trans
  apply mul_le_mul_of_nonneg_right _ (pow_nonneg hε.le 4)
  dsimp only [Cδ]
  linarith

end
end krylov.Functions
