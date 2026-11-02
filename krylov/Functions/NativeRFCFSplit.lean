import krylov.Functions.NativeRFCFDefectJet
import krylov.Functions.RFCFReferenceGeometry

/-!
Article: main_krylov, prop:Fcycle(i), the genuine native model-metric split.
Use: derive a common positive observed denominator and lambda=1/2+O(epsilon)
for every true retained pair, uniformly on the original compact reference
family. Source: actual gradient Taylor errors, native trajectory shadows,
genuine CG orthogonality and the proved real quotient estimate.
-/

namespace krylov.Functions
noncomputable section
open Real Set Metric Filter Topology krylov.Methods krylov.Reference krylov.Nonlinear chebyshev1.Nonlinear
open scoped InnerProductSpace NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

/-- Every true retained RFC-F pair has positive observed curvature and its actual model-metric split is one-half plus a uniform linear error.
Article: main_krylov, prop:Fcycle(i), the complete native split transfer.
The hypotheses are exclusively the original physical derivative conditions
and genuine compact reference nonstagnation. No denominator or split
estimate is assumed. -/
theorem nativeRFCF_split_half (T : E ≃L[ℝ] E)
    (hT : T.symm.toContinuousLinearMap.IsSymmetric)
    (f : E → ℝ) (G : E → E) (H : E → E →L[ℝ] E) (Q : E →L[ℝ] E)
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
    ∃ ε₀ Clam c : ℝ, 0 < ε₀ ∧ 0 < Clam ∧ 0 < c ∧
      ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∀ u : E, ‖u‖ ≤ R → Q u ∈ K → ∀ i : Fin (k+1),
      let a := rfcFAnchors T f G r (ε • u) k i
      let s := rfcFSteps T f G r (ε • u) k i
      c * ε ^ 2 ≤ inner ℝ (G (a+s)-G a) s ∧
        |rfcFSplit T f G r (ε • u) k i - 1 / 2| ≤ Clam * ε := by
  obtain ⟨ep, M, Da, C, hep, hM, _, hC, hprefix⟩ := nativeRFC_compact_prefix T hT f G H Q
    hr hG₀ hH₀ hHc₀ hLr hH hF hG hQ hpos (k+1) K hK hpre R hR
  obtain ⟨c₀, hc₀, henergy⟩ := compact_reference_step_energy Q hQ hpos k K hK hpre
  let P : ℝ := ((‖T.toContinuousLinearMap‖₊ ^ 3 * L : NNReal) : ℝ)
  have hP : 0 ≤ P := NNReal.coe_nonneg _
  let Cs := (2 * (k : ℝ) + 2) * C
  have hCs : 0 ≤ Cs := by dsimp only [Cs]; positivity
  let Cb := 2 * Cs
  let S := 2 * M + Cs
  let Cy := P * M ^ 2 + ‖Q‖ * Cs
  let Y₀ := ‖Q‖ * S
  let My := Cy + Y₀
  let Mb := 2 * M + Cb
  let Ce := Cy * (2 * M) + Y₀ * Cs
  let c := c₀ / 2
  let Clam := (My * Cb + Cy * Mb) / c + 1
  have hCb : 0 ≤ Cb := by dsimp only [Cb]; positivity
  have hS : 0 ≤ S := by dsimp only [S]; positivity
  have hCy : 0 ≤ Cy := by dsimp only [Cy]; positivity
  have hY₀ : 0 ≤ Y₀ := by dsimp only [Y₀]; positivity
  have hMy : 0 ≤ My := by dsimp only [My]; positivity
  have hMb : 0 ≤ Mb := by dsimp only [Mb]; positivity
  have hCe : 0 ≤ Ce := by dsimp only [Ce]; positivity
  have hc : 0 < c := by dsimp only [c]; positivity
  have hClam : 0 < Clam := by dsimp only [Clam]; positivity
  let ε₀ := min ep (min 1 (min (r / (‖T.toContinuousLinearMap‖ * M + 1)) (c₀ / (2 * (Ce + 1)))))
  have hε₀ : 0 < ε₀ := by dsimp only [ε₀]; positivity
  refine ⟨ε₀, Clam, c, hε₀, hClam, hc, ?_⟩
  intro ε hε he u hu hKu i
  dsimp only
  have he₁ : ε ≤ 1 := (he.trans_le ((min_le_right _ _).trans (min_le_left _ _))).le
  have hp := hprefix ε hε (he.trans_le (min_le_left _ _)) u hu hKu
  let a := rfcFAnchors T f G r (ε • u) k i
  let s := rfcFSteps T f G r (ε • u) k i
  let b := a + s
  let x := rfcFAnchor T f G r (ε • u) k
  let q := fcQuadraticReferencePoint Q u
  let σ := referenceStep Q (Q u) i.val
  let y := G b - G a
  let y₀ := Q σ
  let b₀ := q (k+1) - q (i.val+1)
  have hends := hp.rfcF_segments_local T f G H Q r u ε M Da C k i
  have ha : ‖a‖ ≤ M * ε := hends.1
  have hb : ‖b‖ ≤ M * ε := hends.2
  have hx : ‖x‖ ≤ M * ε := (hp.2 k (by omega)).2.2.1
  have hs : ‖s‖ ≤ 2 * M * ε := hp.rfcF_steps_local T f G H Q r u ε M Da C k i
  have hsj : ‖s - ε • σ‖ ≤ Cs * ε ^ 2 := hp.rfcF_reference_steps T f G H Q r u ε M Da C k hC.le i
  have hσ : ‖σ‖ ≤ S := referenceStep_bound_of_shadow s σ ε (2 * M) Cs hε he₁ hCs hs hsj
  have hy₀ : ‖y₀‖ ≤ Y₀ := (Q.le_opNorm σ).trans (mul_le_mul_of_nonneg_left hσ (norm_nonneg _))
  have hlocal (z : E) (hz : ‖z‖ ≤ M * ε) : ‖T z‖ ≤ r := by
    have hh := (T.toContinuousLinearMap.le_opNorm z).trans (mul_le_mul_of_nonneg_left hz (norm_nonneg _))
    change ‖T z‖ ≤ ‖T.toContinuousLinearMap‖ * (M * ε) at hh
    have he' := (lt_div_iff₀ (by positivity : 0 < ‖T.toContinuousLinearMap‖ * M + 1)).mp
      (he.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
    nlinarith only [hh, he', hε]
  have hgrad (z : E) (hz : ‖z‖ ≤ M * ε) : ‖G z - Q z‖ ≤ P / 2 * M ^ 2 * ε ^ 2 := by
    have hh := metric_gradient_quadratic_error T G H Q hr.le hG₀ hH₀ hH hG z (hlocal z hz)
    exact hh.trans ((mul_le_mul_of_nonneg_left
      ((sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hz) (by positivity : 0 ≤ P / 2)).trans_eq (by ring))
  have hy : ‖y - ε • y₀‖ ≤ Cy * ε ^ 2 := by
    have heq : y - ε • y₀ = ((G b - Q b) - (G a - Q a)) + Q (s - ε • σ) := by
      simp only [y, y₀, b, map_sub, map_add, map_smul]
      abel
    rw [heq]
    have hQs : ‖Q (s - ε • σ)‖ ≤ ‖Q‖ * Cs * ε ^ 2 :=
      (Q.le_opNorm _).trans ((mul_le_mul_of_nonneg_left hsj (norm_nonneg _)).trans_eq (by ring))
    exact (norm_add_le _ _).trans ((add_le_add
      ((norm_sub_le _ _).trans (add_le_add (hgrad b hb) (hgrad a ha))) hQs).trans_eq (by dsimp only [Cy]; ring))
  have hyn : ‖y‖ ≤ My * ε := by
    have hh := norm_sub_le (y - ε • y₀) (-ε • y₀)
    have heq : (y - ε • y₀) - -ε • y₀ = y := by module
    rw [heq, norm_smul, norm_neg, Real.norm_of_nonneg hε.le] at hh
    have hε2 : ε ^ 2 ≤ ε := by nlinarith only [hε, he₁]
    have h1 := mul_le_mul_of_nonneg_left hε2 hCy
    have h2 := mul_le_mul_of_nonneg_left hy₀ hε.le
    dsimp only [My]
    nlinarith only [hh, hy, h1, h2]
  have hqstep : q i.val + σ = q (i.val+1) := by
    dsimp only [q, σ]
    rw [← fcQuadraticReferencePoint_step]
    abel
  have hbj : ‖(x - (a + s)) - ε • b₀‖ ≤ Cb * ε ^ 2 := by
    have heq : (x - (a+s)) - ε • b₀ =
        ((x - ε • q (k+1)) - (a - ε • q i.val)) - (s - ε • σ) := by
      rw [show b₀ = q (k+1) - (q i.val + σ) by rw [hqstep]]
      module
    rw [heq]
    have hxa := hp.rfcF_reference_anchor T f G H Q r u ε M Da C k
    have haa := hp.rfcF_reference_anchors T f G H Q r u ε M Da C k i
    have hik : (i.val : ℝ) ≤ (k : ℝ) := by exact_mod_cast Nat.le_of_lt_succ i.isLt
    have haa' : ‖a - ε • q i.val‖ ≤ (k : ℝ) * C * ε ^ 2 := haa.trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hik hC.le) (sq_nonneg ε))
    exact (norm_sub_le _ _).trans ((add_le_add
      ((norm_sub_le _ _).trans (add_le_add hxa haa')) hsj).trans_eq (by dsimp only [Cb, Cs]; ring))
  have hbn : ‖b₀‖ ≤ Mb := by
    have hraw : ‖x - (a+s)‖ ≤ 2 * M * ε :=
      (norm_sub_le _ _).trans ((add_le_add hx hb).trans_eq (by ring))
    exact referenceStep_bound_of_shadow (x - (a+s)) b₀ ε (2*M) Cb hε he₁ hCb hraw hbj
  have hort : inner ℝ y₀ b₀ = 0 := referenceStep_terminal_endpoint_orthogonal Q hQ hpos u k (hpre _ hKu) i
  have hden : c * ε ^ 2 ≤ inner ℝ y s := by
    have herr := secant_energy_shadow y y₀ s σ ε Cy Cs (2*M) Y₀ hε.le hCy hCs
      (by positivity) hY₀ hy hsj hs hy₀
    change |inner ℝ y s - ε ^ 2 * inner ℝ y₀ σ| ≤ Ce * ε ^ 3 at herr
    have hCeε : Ce * ε ≤ c₀ / 2 := by
      have hh := (lt_div_iff₀ (by positivity : 0 < 2 * (Ce + 1))).mp
        (he.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
      nlinarith only [hh, hε]
    have henergy' := henergy (Q u) hKu i
    have h1 := mul_le_mul_of_nonneg_right henergy' (sq_nonneg ε)
    have h2 := mul_le_mul_of_nonneg_right hCeε (sq_nonneg ε)
    have h3 := (abs_le.mp herr).1
    dsimp only [c]
    nlinarith only [h1, h2, h3]
  refine ⟨hden, ?_⟩
  have hsplit := covectorSplit_half_bound y y₀ a s x b₀ ε Cy Cb My Mb c hε hc
    hCy hCb hMy hMb hy hbj hyn hbn hort hden
  change |covectorSplit (innerSL ℝ y) a s x - 1 / 2| ≤ Clam * ε
  exact hsplit.trans (mul_le_mul_of_nonneg_right (by dsimp only [Clam]; linarith) hε.le)

end
end krylov.Functions
