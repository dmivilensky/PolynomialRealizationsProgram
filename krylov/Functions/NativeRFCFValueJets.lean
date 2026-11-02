import krylov.Functions.NativeRFCFSplit
import krylov.Functions.NativeRFCFDefectQuartic

/-!
Article: main_krylov, prop:Fcycle(i), the actual value-corrected model jet.
Use: normalize the real observed diagonal by the square of the initial
source scale and prove its genuine first tensor jet, including the uniform
quadratic remainder for a Lipschitz third derivative. Source: true native
split and defect transfers; all function values are actual oracle values.
-/

namespace krylov.Functions
noncomputable section
open Real Set Metric Filter Topology krylov.Methods krylov.Reference krylov.Nonlinear chebyshev1.Nonlinear
open scoped InnerProductSpace NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual observed diagonal change in chronological retained-step coordinates, normalized by the source scale squared.
Article: main_krylov, prop:Fcycle(i), before reversal and last-column rescaling. -/
def rfcFNormalizedValueDiagonal (T : E ≃L[ℝ] E) (f : E → ℝ) (G : E → E)
    (r : ℝ) (x₀ : E) (k : ℕ) (ε : ℝ) (i : Fin (k+1)) : ℝ :=
  (-12 * rfcFSplit T f G r x₀ k i * segmentValueDefect f (fun x => innerSL ℝ (G x))
    (rfcFAnchors T f G r x₀ k i) (rfcFSteps T f G r x₀ k i)) / ε ^ 2

/-- Every true bounded compact CG reference gives a bounded cubic diagonal coefficient.
Article: main_krylov, prop:Fcycle(i), genuine reference tensor source control. -/
theorem compact_reference_cubic_bound (Q : E →L[ℝ] E)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E, v ≠ 0 → 0 < inner ℝ v (Q v))
    (D : E →L[ℝ] E →L[ℝ] E) (k : ℕ) (K : Set E) (hK : IsCompact K)
    (hpre : ∀ g ∈ K, ∀ i < k+1, CG.gradient Q g i ≠ 0) :
    ∃ B : ℝ, 0 < B ∧ ∀ g ∈ K, ∀ i : Fin (k+1),
      |inner ℝ (D (referenceStep Q g i.val) (referenceStep Q g i.val))
        (referenceStep Q g i.val)| ≤ B := by
  obtain ⟨M, hM, hnorm⟩ := compact_reference_step_norm Q hQ hpos k K hK hpre
  refine ⟨‖D‖ * M ^ 3 + 1, by positivity, ?_⟩
  intro g hg i
  let σ := referenceStep Q g i.val
  calc
    _ ≤ ‖D‖ * ‖σ‖ * ‖σ‖ * ‖σ‖ := inner_third_bound D σ σ σ
    _ = ‖D‖ * ‖σ‖ ^ 3 := by ring
    _ ≤ ‖D‖ * M ^ 3 := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) (hnorm g hg i) 3) (norm_nonneg D)
    _ ≤ _ := by linarith

variable [CompleteSpace E] [FiniteDimensional ℝ E]

/-- The actual normalized RFC-F model diagonal has the source's one-half third-derivative jet, uniformly on compact nondegenerate references.
Article: main_krylov, prop:Fcycle(i), the complete physical diagonal transfer.
Only original physical derivatives and real reference nonstagnation are
assumed; both actual split and actual observed defect jets are proved inputs. -/
theorem nativeRFCF_value_diagonal_jet (T : E ≃L[ℝ] E)
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
      |rfcFNormalizedValueDiagonal T f G r (ε • u) k ε i -
        ε / 2 * inner ℝ (D (referenceStep Q (Q u) i.val) (referenceStep Q (Q u) i.val))
          (referenceStep Q (Q u) i.val)| ≤ η * ε := by
  obtain ⟨es, Clam, c, hes, hClam, _, hsplit⟩ := nativeRFCF_split_half T hT f G H Q
    hr hG₀ hH₀ hHc₀ hLr hH hF hG hQ hpos k K hK hpre R hR
  obtain ⟨B, hB, hcoeff⟩ := compact_reference_cubic_bound Q hQ hpos D k K hK hpre
  intro η hη
  let ζ := η / (24 * (Clam + 1))
  have hζ : 0 < ζ := by dsimp only [ζ]; positivity
  obtain ⟨ed, hed, hdefect⟩ := nativeRFCF_value_defect_jet T hT f G H Q D hD
    hr hG₀ hH₀ hHc₀ hLr hH hF hG hQ hpos k K hK hpre R hR ζ hζ
  let ε₀ := min es (min ed (min 1 (η / (2 * (Clam * B + 1)))))
  have hε₀ : 0 < ε₀ := by dsimp only [ε₀]; positivity
  refine ⟨ε₀, hε₀, ?_⟩
  intro ε hε he u hu hKu i
  have hl := (hsplit ε hε (he.trans_le (min_le_left _ _)) u hu hKu i).2
  have hd := hdefect ε hε (he.trans_le ((min_le_right _ _).trans (min_le_left _ _))) u hu hKu i
  have ht := hcoeff (Q u) hKu i
  have he₁ : ε ≤ 1 := (he.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))).le
  have hh := normalized_value_correction_bound _ _ _ ε Clam B ζ hε he₁ hClam.le hB.le hζ.le hl ht hd
  change |rfcFNormalizedValueDiagonal T f G r (ε • u) k ε i - _| ≤ _ at hh
  apply hh.trans
  have hfirst : 12 * (Clam + 1) * ζ = η / 2 := by dsimp only [ζ]; field_simp; ring
  have hsecond : Clam * B * ε ≤ η / 2 := by
    have hb := (lt_div_iff₀ (by positivity : 0 < 2 * (Clam * B + 1))).mp
      (he.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
    nlinarith only [hb, hε]
  rw [hfirst]
  nlinarith only [mul_le_mul_of_nonneg_right hsecond hε.le]

/-- Lipschitz original third derivatives give a genuine uniform quadratic remainder in the actual normalized value-model diagonal.
Article: main_krylov, prop:Fcycle(i), the fourth-order cycle-transfer input. -/
theorem nativeRFCF_value_diagonal_quartic (T : E ≃L[ℝ] E)
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
    ∃ ε₀ Cj : ℝ, 0 < ε₀ ∧ 0 < Cj ∧
      ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∀ u : E, ‖u‖ ≤ R → Q u ∈ K → ∀ i : Fin (k+1),
      |rfcFNormalizedValueDiagonal T f G r (ε • u) k ε i -
        ε / 2 * inner ℝ (D 0 (referenceStep Q (Q u) i.val) (referenceStep Q (Q u) i.val))
          (referenceStep Q (Q u) i.val)| ≤ Cj * ε ^ 2 := by
  obtain ⟨es, Clam, c, hes, hClam, _, hsplit⟩ := nativeRFCF_split_half T hT f G H Q
    hr hG₀ hH₀ hHc₀ hLr hH hF hG hQ hpos k K hK hpre R hR
  obtain ⟨B, hB, hcoeff⟩ := compact_reference_cubic_bound Q hQ hpos (D 0) k K hK hpre
  obtain ⟨ed, Cd, hed, hCd, hdefect⟩ := nativeRFCF_value_defect_quartic T hT f G H Q D
    hr hG₀ hH₀ hHc₀ hLr hH hD hDlip hF hG hQ hpos k K hK hpre R hR
  let Cj := 12 * (Clam + 1) * Cd + Clam * B
  have hCj : 0 < Cj := by dsimp only [Cj]; positivity
  refine ⟨min es (min ed 1), Cj, lt_min hes (lt_min hed (by norm_num)), hCj, ?_⟩
  intro ε hε he u hu hKu i
  have hl := (hsplit ε hε (he.trans_le (min_le_left _ _)) u hu hKu i).2
  have hd := hdefect ε hε (he.trans_le ((min_le_right _ _).trans (min_le_left _ _))) u hu hKu i
  have ht := hcoeff (Q u) hKu i
  have he₁ : ε ≤ 1 := (he.trans_le ((min_le_right _ _).trans (min_le_right _ _))).le
  have hd' : |segmentValueDefect f (fun x => innerSL ℝ (G x))
      (rfcFAnchors T f G r (ε • u) k i) (rfcFSteps T f G r (ε • u) k i) +
        ε ^ 3 * inner ℝ (D 0 (referenceStep Q (Q u) i.val) (referenceStep Q (Q u) i.val))
          (referenceStep Q (Q u) i.val) / 12| ≤ (Cd * ε) * ε ^ 3 := hd.trans_eq (by ring)
  have hh := normalized_value_correction_bound _ _ _ ε Clam B (Cd * ε) hε he₁ hClam.le hB.le
    (mul_nonneg hCd.le hε.le) hl ht hd'
  change |rfcFNormalizedValueDiagonal T f G r (ε • u) k ε i - _| ≤ _ at hh
  exact hh.trans_eq (by dsimp only [Cj]; ring)

end
end krylov.Functions
