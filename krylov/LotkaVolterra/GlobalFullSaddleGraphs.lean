import krylov.LotkaVolterra.GlobalGraphCoordinates

/-!
Article: `main_krylov`, `apC:prop:LV`, complete state ranges of the stable
graphs. The two functions below are constructed from whole-line shooting,
and satisfy the exact LV graph equation throughout their open state ranges.

Source: logistic compactification, compact shooting and inverse-coordinate
differentiation; no global stable graph is assumed.
-/
namespace krylov.LotkaVolterra
noncomputable section
open Set

def graphFromSlope (γ : ℝ) (T : ℝ → ℝ) (v : ℝ → ℝ) (U : ℝ) : ℝ :=
  saddleS γ - v (T U) * (saddleU γ - U)

theorem graphRate_from_chord {γ U v : ℝ} (hγ : γ ≠ 1) (hU : U ≠ 0)
    (hz : saddleU γ - U ≠ 0) (hv : 1 - v ≠ 0) :
    v + saddleSlopeRate γ (saddleU γ - U) v =
      2 * (saddleS γ - v * (saddleU γ - U)) *
        (saddleS γ - v * (saddleU γ - U) - 1 - γ * U) /
          (U * (saddleS γ - v * (saddleU γ - U) + 1 - U)) := by
  have hA := saddleS_eq_one_add_mul_saddleU hγ
  have hB := saddleU_eq_saddleS_add_one hγ
  have h₁ : saddleS γ - v * (saddleU γ - U) - 1 - γ * U =
      (saddleU γ - U) * (γ - v) := by rw [hA]; ring
  have h₂ : saddleS γ - v * (saddleU γ - U) + 1 - U =
      (saddleU γ - U) * (1 - v) := by rw [hB]; ring
  rw [h₁, h₂]
  unfold saddleSlopeRate
  have he : saddleU γ - (saddleU γ - U) = U := by ring
  rw [he]
  field_simp
  ring

theorem exists_global_lower_graph {γ : ℝ} (hγ : 0 < γ) (hγ₁ : γ < 1) :
    ∃ σ : ℝ → ℝ, ∀ U ∈ Ioo (0 : ℝ) (saddleU γ),
      1 + γ * U < σ U ∧ σ U < saddleS γ ∧ U - 1 < σ U ∧
      HasDerivAt σ (2 * σ U * (σ U - 1 - γ * U) / (U * (σ U + 1 - U))) U := by
  obtain ⟨v, hv⟩ := exists_whole_logistic_slope hγ hγ₁ true
  let σ := graphFromSlope γ (lowerGraphTime γ) v
  refine ⟨σ, fun U hU ↦ ?_⟩
  let τ := lowerGraphTime γ U
  have hvr := hv τ
  have hB := saddleU_pos hγ₁
  have hZ := sub_pos.mpr hU.2
  have hV : 0 < 1 - v τ := by linarith [hvr.1.2]
  have hAeq := saddleS_eq_one_add_mul_saddleU (ne_of_lt hγ₁)
  have hBeq := saddleU_eq_saddleS_add_one (ne_of_lt hγ₁)
  have hcomp := hvr.2.comp U (lowerGraphTime_hasDerivAt hU)
  rw [lowerGraphTime_parameter hγ₁ hU,
    lowerLogisticRate_eq (ne_of_gt hB) (ne_of_gt hU.1) (ne_of_gt hV)] at hcomp
  have hcomp' : HasDerivAt (fun U ↦ v (lowerGraphTime γ U))
      (-saddleSlopeRate γ (saddleU γ - U) (v τ) / (saddleU γ - U)) U := by
    convert hcomp using 1
    · rfl
    · field_simp [ne_of_gt hU.1, ne_of_gt hB, ne_of_gt hZ]
  have hS := (hcomp'.mul ((hasDerivAt_id U).const_sub (saddleU γ))).const_sub (saddleS γ)
  have hd : HasDerivAt σ (v τ + saddleSlopeRate γ (saddleU γ - U) (v τ)) U := by
    convert hS using 1
    · rfl
    · dsimp only [id_eq]
      rw [div_mul_cancel₀ _ (ne_of_gt hZ)]
      dsimp [τ]
      ring
  have hbound₁ : 1 + γ * U < σ U := by
    have hh := mul_pos hZ (sub_pos.mpr hvr.1.2)
    dsimp [σ, graphFromSlope]
    rw [hAeq]
    nlinarith
  have hbound₂ : σ U < saddleS γ := by
    have hh := mul_pos hvr.1.1 hZ
    dsimp [σ, graphFromSlope]
    linarith
  have hbound₃ : U - 1 < σ U := by
    have hh := mul_pos hZ hV
    dsimp [σ, graphFromSlope]
    rw [hBeq] at hh ⊢
    nlinarith
  refine ⟨hbound₁, hbound₂, hbound₃, ?_⟩
  simpa only [graphRate_from_chord (ne_of_lt hγ₁) (ne_of_gt hU.1)
    (ne_of_gt hZ) (ne_of_gt hV), σ, graphFromSlope, τ] using hd

theorem exists_global_upper_graph {γ : ℝ} (hγ : 0 < γ) (hγ₁ : γ < 1) :
    ∃ σ : ℝ → ℝ, ∀ U > saddleU γ,
      saddleS γ < σ U ∧ σ U < 1 + γ * U ∧ σ U < U - 1 ∧
      HasDerivAt σ (2 * σ U * (σ U - 1 - γ * U) / (U * (σ U + 1 - U))) U := by
  obtain ⟨v, hv⟩ := exists_whole_logistic_slope hγ hγ₁ false
  let σ := graphFromSlope γ (upperGraphTime γ) v
  refine ⟨σ, fun U hU ↦ ?_⟩
  let τ := upperGraphTime γ U
  have hvr := hv τ
  have hB := saddleU_pos hγ₁
  have hUp := hB.trans hU
  have hZ := sub_pos.mpr hU
  have hV : 0 < 1 - v τ := by linarith [hvr.1.2]
  have hAeq := saddleS_eq_one_add_mul_saddleU (ne_of_lt hγ₁)
  have hBeq := saddleU_eq_saddleS_add_one (ne_of_lt hγ₁)
  have hcomp := hvr.2.comp U (upperGraphTime_hasDerivAt hγ₁ hU)
  rw [upperGraphTime_parameter hγ₁ hU,
    upperLogisticRate_eq (ne_of_gt hB) (ne_of_gt hUp) (ne_of_gt hV)] at hcomp
  have hcomp' : HasDerivAt (fun U ↦ v (upperGraphTime γ U))
      (-saddleSlopeRate γ (saddleU γ - U) (v τ) / (saddleU γ - U)) U := by
    convert hcomp using 1
    · rfl
    · field_simp [ne_of_gt hZ, sub_ne_zero.mpr (ne_of_lt hU)]
      ring
  have hS := (hcomp'.mul ((hasDerivAt_id U).const_sub (saddleU γ))).const_sub (saddleS γ)
  have hd : HasDerivAt σ (v τ + saddleSlopeRate γ (saddleU γ - U) (v τ)) U := by
    convert hS using 1
    · rfl
    · dsimp only [id_eq]
      rw [div_mul_cancel₀ _ (sub_ne_zero.mpr (ne_of_lt hU))]
      dsimp [τ]
      ring
  have hbound₁ : saddleS γ < σ U := by
    have hh := mul_pos hvr.1.1 hZ
    dsimp [σ, graphFromSlope]
    nlinarith
  have hbound₂ : σ U < 1 + γ * U := by
    have hh := mul_pos hZ (sub_pos.mpr hvr.1.2)
    dsimp [σ, graphFromSlope]
    rw [hAeq]
    nlinarith
  have hbound₃ : σ U < U - 1 := by
    have hh := mul_pos hZ hV
    dsimp [σ, graphFromSlope]
    rw [hBeq] at hh ⊢
    nlinarith
  refine ⟨hbound₁, hbound₂, hbound₃, ?_⟩
  simpa only [graphRate_from_chord (ne_of_lt hγ₁) (ne_of_gt hUp)
    (sub_ne_zero.mpr (ne_of_lt hU)) (ne_of_gt hV), σ, graphFromSlope, τ] using hd

end
end krylov.LotkaVolterra
