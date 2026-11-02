import krylov.LotkaVolterra.GlobalSaddleField
import krylov.LotkaVolterra.GlobalStripShooting
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
Article: `main_krylov`, `apC:prop:LV`, existence of bounded saddle slopes.

Compact shooting is applied to the actual regularized chord-slope equation.
For either sign of the saddle distance this constructs an integral curve
on the entire half-line approaching the saddle, without invoking a stable
manifold theorem or assuming the desired graph.

Source: logarithmic saddle coordinates and the compact strip construction
in `GlobalStripShooting`.
-/
namespace krylov.LotkaVolterra
noncomputable section
open Set
open scoped NNReal

/-- Signed distance from the saddle. Clipping negative logarithmic times
only extends the field outside the half-line used in the conclusion. -/
def saddleDistance (γ ε t : ℝ) : ℝ :=
  ε * (saddleU γ / 2) * Real.exp (-max 0 t)

theorem saddleDistance_mem {γ ε : ℝ} (hγ₁ : γ < 1) (hε : |ε| ≤ 1) (t : ℝ) :
    saddleDistance γ ε t ∈ Icc (-(saddleU γ / 2)) (saddleU γ / 2) := by
  have hc : 0 ≤ saddleU γ / 2 := (half_pos (saddleU_pos hγ₁)).le
  have hE : 0 ≤ Real.exp (-max 0 t) := (Real.exp_pos _).le
  have hE₁ : Real.exp (-max 0 t) ≤ 1 := Real.exp_le_one_iff.mpr (by
    linarith [le_max_left (0 : ℝ) t])
  have hW : 0 ≤ saddleU γ / 2 * Real.exp (-max 0 t) := mul_nonneg hc hE
  have hW₁ : saddleU γ / 2 * Real.exp (-max 0 t) ≤ saddleU γ / 2 := by
    simpa using mul_le_mul_of_nonneg_left hE₁ hc
  have hε' := abs_le.mp hε
  have hlo := mul_le_mul_of_nonneg_right hε'.1 hW
  have hhi := mul_le_mul_of_nonneg_right hε'.2 hW
  dsimp [saddleDistance]
  constructor <;> nlinarith [hlo, hhi]

theorem saddleDistance_continuous (γ ε : ℝ) : Continuous (saddleDistance γ ε) := by
  unfold saddleDistance
  fun_prop

/-- Reversed logarithmic slope field, extended by clipping the slope. -/
def clippedSaddleSlopeRate (γ ε t v : ℝ) : ℝ :=
  -saddleSlopeRate γ (saddleDistance γ ε t) (saddleSlopeClip γ v)

theorem clippedSaddleSlopeRate_continuous_time {γ ε : ℝ} (hγ : 0 < γ)
    (hγ₁ : γ < 1) (hε : |ε| ≤ 1) (v : ℝ) :
    Continuous (fun t ↦ clippedSaddleSlopeRate γ ε t v) := by
  have hZ := saddleDistance_continuous γ ε
  have hden (t : ℝ) : saddleU γ - saddleDistance γ ε t ≠ 0 :=
    ne_of_gt (saddleSlope_denominators hγ₁
      (p := (saddleDistance γ ε t, saddleSlopeClip γ v))
      ⟨saddleDistance_mem hγ₁ hε t, saddleSlopeClip_mem hγ.le v⟩).1
  unfold clippedSaddleSlopeRate saddleSlopeRate
  exact ((((continuous_const.sub (continuous_const.mul hZ)).const_mul 2).div
    (continuous_const.sub hZ) hden).mul continuous_const).sub continuous_const |>.neg

theorem clippedSaddleSlopeRate_bounds {γ ε : ℝ} (hγ : 0 < γ)
    (hγ₁ : γ < 1) (hε : |ε| ≤ 1) :
    ∃ L K : ℝ≥0, (∀ t v, ‖clippedSaddleSlopeRate γ ε t v‖ ≤ L) ∧
      ∀ t, LipschitzWith K (clippedSaddleSlopeRate γ ε t) := by
  obtain ⟨L, K, hL, hK⟩ := saddleSlopeRate_uniform_bounds hγ₁
  refine ⟨L, K, ?_, fun t ↦ ?_⟩
  · intro t v
    simpa [clippedSaddleSlopeRate] using hL _ (saddleDistance_mem hγ₁ hε t)
      _ (saddleSlopeClip_mem hγ.le v)
  · apply LipschitzWith.of_dist_le_mul
    intro v w
    calc
      dist (clippedSaddleSlopeRate γ ε t v) (clippedSaddleSlopeRate γ ε t w) =
          dist (saddleSlopeRate γ (saddleDistance γ ε t) (saddleSlopeClip γ v))
            (saddleSlopeRate γ (saddleDistance γ ε t) (saddleSlopeClip γ w)) := by
        simp [clippedSaddleSlopeRate]
      _ ≤ K * dist (saddleSlopeClip γ v) (saddleSlopeClip γ w) :=
        (hK _ (saddleDistance_mem hγ₁ hε t)).dist_le_mul
          _ (saddleSlopeClip_mem hγ.le v) _ (saddleSlopeClip_mem hγ.le w)
      _ ≤ K * dist v w := by
        gcongr
        simpa using (saddleSlopeClip_lipschitz γ).dist_le_mul v w

/-- Actual bounded chord-slope trajectories exist on both sides of the
subcritical saddle. The decay parameter is genuine: `z = ε U_F exp(-t)/2`.
For `ε = ±1` these are the two nonconstant stable branches. -/
theorem exists_bounded_saddle_slope {γ ε : ℝ} (hγ : 0 < γ)
    (hγ₁ : γ < 1) (hε : |ε| ≤ 1) :
    ∃ v : ℝ → ℝ, ∀ t ≥ 0, v t ∈ Icc 0 γ ∧
      HasDerivAt v (-saddleSlopeRate γ (ε * (saddleU γ / 2) * Real.exp (-t)) (v t)) t := by
  obtain ⟨L, K, hbound, hLip⟩ := clippedSaddleSlopeRate_bounds hγ hγ₁ hε
  have ha : ∀ t ≥ (0 : ℝ), clippedSaddleSlopeRate γ ε t 0 < 0 := by
    intro t _
    rw [clippedSaddleSlopeRate, saddleSlopeClip_eq (show (0 : ℝ) ∈ Icc 0 γ by
      exact ⟨le_rfl, hγ.le⟩)]
    exact neg_neg_of_pos (saddleSlopeRate_zero_pos hγ hγ₁ (saddleDistance_mem hγ₁ hε t))
  have hb : ∀ t ≥ (0 : ℝ), 0 < clippedSaddleSlopeRate γ ε t γ := by
    intro t _
    rw [clippedSaddleSlopeRate, saddleSlopeClip_eq (show γ ∈ Icc 0 γ by
      exact ⟨hγ.le, le_rfl⟩), saddleSlopeRate_gamma]
    simpa using hγ
  obtain ⟨v, hv⟩ := exists_forward_strip_solution hLip
    (clippedSaddleSlopeRate_continuous_time hγ hγ₁ hε) hbound hγ ha hb
  refine ⟨v, fun t ht ↦ ⟨(hv t ht).1, ?_⟩⟩
  simpa only [clippedSaddleSlopeRate, saddleSlopeClip_eq (hv t ht).1,
    saddleDistance, max_eq_right ht] using (hv t ht).2

end
end krylov.LotkaVolterra
