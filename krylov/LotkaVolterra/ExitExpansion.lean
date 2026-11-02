import krylov.LotkaVolterra.GlobalSaddleContraction

/-!
Article: main_krylov, apC:prop:LV, exit classification.
Use: uniform expansion of the reverse chord equation over the entire lower
physical region U≥1, not only in a small neighborhood of the saddle.
Source: the exact derivative factorization and the mean-value theorem.
-/

namespace krylov.LotkaVolterra
noncomputable section
open Set

theorem saddleSlopeDerivative_le_neg_one_lower {γ z v : ℝ} (hγ : γ < 1)
    (hz : z ∈ Icc (0 : ℝ) (saddleS γ)) (hv : v < 1) :
    saddleSlopeDerivative γ z v ≤ -1 := by
  have hB := saddleU_eq_saddleS_add_one (ne_of_lt hγ)
  have hden : 0 < saddleU γ - z := by linarith [hz.2]
  have hA : (1 - γ) * saddleS γ = 1 + γ := by
    unfold saddleS
    field_simp [ne_of_gt (sub_pos.mpr hγ)]
  have hN : 0 ≤ (1 + γ) - (1 - γ) * z := by
    have hh := mul_le_mul_of_nonneg_left hz.2 (sub_nonneg.mpr hγ.le)
    rw [hA] at hh
    linarith
  rw [saddleSlopeDerivative_factor hγ hden.ne' (by linarith : 1 - v ≠ 0)]
  have hfirst : -(saddleU γ + z) / (saddleU γ - z) ≤ -1 := by
    apply (div_le_iff₀ hden).mpr
    linarith [hz.1]
  have hsecond : 0 ≤ 2 * ((1 + γ) - (1 - γ) * z) /
      ((saddleU γ - z) * (1 - v) ^ 2) := by positivity
  linarith

/-- Two bounded lower-region chord slopes separate at a uniform rate unless
they coincide. This is the scalar input for the actual nonexit alternative. -/
theorem saddleSlopeRate_lower_expansion {γ z v w : ℝ} (hγ : γ < 1)
    (hz : z ∈ Icc (0 : ℝ) (saddleS γ))
    (hv : v ∈ Icc 0 γ) (hw : w ∈ Icc 0 γ) :
    (v - w) ^ 2 ≤ (v - w) * (-saddleSlopeRate γ z v + saddleSlopeRate γ z w) := by
  let g : ℝ → ℝ := fun v ↦ -saddleSlopeRate γ z v
  have hd (v : ℝ) (hv : v ∈ Icc 0 γ) : HasDerivAt g (-saddleSlopeDerivative γ z v) v :=
    (saddleSlopeRate_hasDerivAt (by linarith [hv.2] : 1 - v ≠ 0)).neg
  have hMVT := (convex_Icc (0 : ℝ) γ).mul_sub_le_image_sub_of_le_deriv
    (HasDerivAt.continuousOn fun v hv ↦ hd v hv)
    (fun v hv ↦ (hd v (interior_subset hv)).differentiableAt.differentiableWithinAt)
    (C := (1 : ℝ)) (fun v hv ↦ by
      rw [(hd v (interior_subset hv)).deriv]
      linarith [saddleSlopeDerivative_le_neg_one_lower hγ hz
        (show v < 1 from (interior_subset hv).2.trans_lt hγ)])
  rcases le_total w v with hwv | hvw
  · have hm := mul_le_mul_of_nonneg_left (hMVT w hw v hv hwv) (sub_nonneg.mpr hwv)
    dsimp [g] at hm
    nlinarith
  · have hm := mul_le_mul_of_nonneg_left (hMVT v hv w hw hvw) (sub_nonneg.mpr hvw)
    dsimp [g] at hm
    nlinarith

end
end krylov.LotkaVolterra
