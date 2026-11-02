import krylov.LotkaVolterra.GlobalSaddleBranches
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
Article: `main_krylov`, uniqueness of the constructed stable branches.

The saddle chord equation is uniformly contracting in increasing logarithmic
distance: its slope derivative is at most `-1/3` on the entire chosen
rectangle, for both signs of the distance. After time reversal this gives
the same strict expansion principle as endpoint graph uniqueness.

Source: direct factorization of the rational derivative, followed by the
scalar mean-value theorem.
-/
namespace krylov.LotkaVolterra
noncomputable section
open Set

theorem saddleSlopeDerivative_factor {γ z v : ℝ} (hγ₁ : γ < 1)
    (hz : saddleU γ - z ≠ 0) (hv : 1 - v ≠ 0) :
    saddleSlopeDerivative γ z v =
      -(saddleU γ + z) / (saddleU γ - z) -
        2 * ((1 + γ) - (1 - γ) * z) / ((saddleU γ - z) * (1 - v) ^ 2) := by
  have hA : (1 - γ) * saddleS γ = 1 + γ := by
    unfold saddleS
    field_simp [ne_of_gt (sub_pos.mpr hγ₁)]
  unfold saddleSlopeDerivative
  field_simp
  nlinarith only [hA]

theorem saddleSlopeDerivative_le_neg_third {γ z v : ℝ}
    (hγ : 0 < γ) (hγ₁ : γ < 1)
    (hz : z ∈ Icc (-(saddleU γ / 2)) (saddleU γ / 2)) (hv : v ∈ Icc 0 γ) :
    saddleSlopeDerivative γ z v ≤ -(1 / 3 : ℝ) := by
  have hpos := saddleSlope_denominators hγ₁ (p := (z, v)) ⟨hz, hv⟩
  have hB : (1 - γ) * saddleU γ = 2 := by
    unfold saddleU
    field_simp [ne_of_gt (sub_pos.mpr hγ₁)]
  have hmul := mul_le_mul_of_nonneg_left hz.2 (sub_pos.mpr hγ₁).le
  have hN : 0 ≤ (1 + γ) - (1 - γ) * z := by nlinarith
  have hden : 0 < (saddleU γ - z) * (1 - v) ^ 2 :=
    mul_pos hpos.1 (sq_pos_of_pos hpos.2)
  have hq : (1 / 3 : ℝ) ≤ (saddleU γ + z) / (saddleU γ - z) := by
    apply (le_div_iff₀ hpos.1).mpr
    linarith [hz.1]
  have hr : 0 ≤ 2 * ((1 + γ) - (1 - γ) * z) /
      ((saddleU γ - z) * (1 - v) ^ 2) := div_nonneg (by positivity) hden.le
  rw [saddleSlopeDerivative_factor hγ₁ (ne_of_gt hpos.1) (ne_of_gt hpos.2)]
  rw [neg_div]
  linarith

/-- Quantitative expansion of the time-reversed saddle equation. -/
theorem saddleSlopeRate_expansion {γ z v w : ℝ} (hγ : 0 < γ) (hγ₁ : γ < 1)
    (hz : z ∈ Icc (-(saddleU γ / 2)) (saddleU γ / 2))
    (hv : v ∈ Icc 0 γ) (hw : w ∈ Icc 0 γ) :
    (v - w) ^ 2 / 3 ≤ (v - w) * (-saddleSlopeRate γ z v + saddleSlopeRate γ z w) := by
  let g : ℝ → ℝ := fun v ↦ -saddleSlopeRate γ z v
  have hd (v : ℝ) (hv : v ∈ Icc 0 γ) : HasDerivAt g (-saddleSlopeDerivative γ z v) v :=
    (saddleSlopeRate_hasDerivAt (ne_of_gt
      (saddleSlope_denominators hγ₁ (p := (z, v)) ⟨hz, hv⟩).2)).neg
  have hMVT := (convex_Icc (0 : ℝ) γ).mul_sub_le_image_sub_of_le_deriv
    (HasDerivAt.continuousOn fun v hv ↦ hd v hv)
    (fun v hv ↦ (hd v (interior_subset hv)).differentiableAt.differentiableWithinAt)
    (C := (1 / 3 : ℝ)) (fun v hv ↦ by
      rw [(hd v (interior_subset hv)).deriv]
      linarith [saddleSlopeDerivative_le_neg_third hγ hγ₁ hz (interior_subset hv)])
  rcases le_total w v with hwv | hvw
  · have hh := hMVT w hw v hv hwv
    have hm := mul_le_mul_of_nonneg_left hh (sub_nonneg.mpr hwv)
    dsimp [g] at hm
    nlinarith
  · have hh := hMVT v hv w hw hvw
    have hm := mul_le_mul_of_nonneg_left hh (sub_nonneg.mpr hvw)
    dsimp [g] at hm
    nlinarith

end
end krylov.LotkaVolterra
