import krylov.LotkaVolterra.GlobalLogisticShooting
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
Exact inverse graph coordinates for the full subcritical branches. Source:
differentiate the logarithmic substitutions in `GlobalLogisticShooting`.
-/
namespace krylov.LotkaVolterra
noncomputable section
open Set

def lowerGraphTime (γ U : ℝ) : ℝ := Real.log (U / (saddleU γ - U))
def upperGraphTime (γ U : ℝ) : ℝ := Real.log (saddleU γ / (U - saddleU γ))

theorem lowerGraphTime_parameter {γ U : ℝ} (hγ₁ : γ < 1)
    (hU : U ∈ Ioo 0 (saddleU γ)) :
    logisticParameter (lowerGraphTime γ U) = (saddleU γ - U) / saddleU γ := by
  have hB := saddleU_pos hγ₁
  have hd := sub_pos.mpr hU.2
  unfold logisticParameter lowerGraphTime
  rw [Real.exp_log (div_pos hU.1 hd)]
  field_simp [ne_of_gt hB, ne_of_gt hd]
  ring

theorem upperGraphTime_parameter {γ U : ℝ} (hγ₁ : γ < 1) (hU : saddleU γ < U) :
    logisticParameter (upperGraphTime γ U) = (U - saddleU γ) / U := by
  have hB := saddleU_pos hγ₁
  have hd := sub_pos.mpr hU
  unfold logisticParameter upperGraphTime
  rw [Real.exp_log (div_pos hB hd)]
  field_simp [ne_of_gt hB, ne_of_gt hd, ne_of_gt (hB.trans hU)]
  ring

theorem lowerGraphTime_hasDerivAt {γ U : ℝ}
    (hU : U ∈ Ioo 0 (saddleU γ)) :
    HasDerivAt (lowerGraphTime γ) (saddleU γ / (U * (saddleU γ - U))) U := by
  have hd := sub_pos.mpr hU.2
  have hh := ((hasDerivAt_id U).div ((hasDerivAt_id U).const_sub (saddleU γ))
    (ne_of_gt hd)).log (ne_of_gt (div_pos hU.1 hd))
  convert hh using 1
  · rfl
  · dsimp
    field_simp [ne_of_gt hd, ne_of_gt hU.1]
    ring

theorem upperGraphTime_hasDerivAt {γ U : ℝ} (hγ₁ : γ < 1) (hU : saddleU γ < U) :
    HasDerivAt (upperGraphTime γ) (-(1 / (U - saddleU γ))) U := by
  have hB := saddleU_pos hγ₁
  have hd := sub_pos.mpr hU
  have hh := ((hasDerivAt_const U (saddleU γ)).div ((hasDerivAt_id U).sub_const (saddleU γ))
    (ne_of_gt hd)).log (ne_of_gt (div_pos hB hd))
  convert hh using 1
  · rfl
  · dsimp
    field_simp [ne_of_gt hd, ne_of_gt hB]
    ring

theorem lowerLogisticRate_eq {γ U v : ℝ} (hB : saddleU γ ≠ 0) (hU : U ≠ 0)
    (hv : 1 - v ≠ 0) :
    logisticSlopeRate γ true ((saddleU γ - U) / saddleU γ) v =
      -(U / saddleU γ) * saddleSlopeRate γ (saddleU γ - U) v := by
  unfold logisticSlopeRate logisticP logisticQ logisticR saddleSlopeRate
  simp only [ite_true]
  have he : saddleU γ - (saddleU γ - U) = U := by ring
  rw [he]
  field_simp
  ring

theorem upperLogisticRate_eq {γ U v : ℝ} (hB : saddleU γ ≠ 0) (hU : U ≠ 0)
    (hv : 1 - v ≠ 0) :
    logisticSlopeRate γ false ((U - saddleU γ) / U) v =
      -saddleSlopeRate γ (saddleU γ - U) v := by
  unfold logisticSlopeRate logisticP logisticQ logisticR saddleSlopeRate
  simp only [Bool.false_eq_true, ite_false]
  have he : saddleU γ - (saddleU γ - U) = U := by ring
  rw [he]
  field_simp
  ring

end
end krylov.LotkaVolterra
