import krylov.LotkaVolterra.GlobalCompactField
import krylov.LotkaVolterra.Basic
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic

/-!
Article: `main_krylov`, `apC:prop:LV`, constructive saddle coordinates.

For `z = U_F-U` and `s = s_F-vz`, the invariance equation becomes
`z dv/dz = H(z,v)`. In logarithmic distance from the saddle it is a regular
scalar equation. Its strip `0 ≤ v ≤ γ` points inward in increasing `log |z|`.
The rational field has uniform bounds on a concrete compact rectangle.

Source: direct substitution in the article's LV system, combined with the
standard compactness and mean-value argument of `GlobalCompactField`.
-/
namespace krylov.LotkaVolterra
noncomputable section
open Set
open scoped NNReal

/-- Chord-slope equation at the subcritical saddle. -/
def saddleSlopeRate (γ z v : ℝ) : ℝ :=
  (2 * (saddleS γ - v * z) / (saddleU γ - z)) * ((γ - v) / (1 - v)) - v

/-- Explicit derivative in the slope variable. -/
def saddleSlopeDerivative (γ z v : ℝ) : ℝ :=
  (-2 * z / (saddleU γ - z)) * ((γ - v) / (1 - v)) +
    (2 * (saddleS γ - v * z) / (saddleU γ - z)) * ((γ - 1) / (1 - v) ^ 2) - 1

theorem saddleSlopeRate_hasDerivAt {γ z v : ℝ} (hv : 1 - v ≠ 0) :
    HasDerivAt (saddleSlopeRate γ z) (saddleSlopeDerivative γ z v) v := by
  have hA := ((hasDerivAt_const v (saddleS γ)).sub ((hasDerivAt_id v).mul_const z))
    |>.const_mul 2 |>.div_const (saddleU γ - z)
  have hB := ((hasDerivAt_id v).const_sub γ).div ((hasDerivAt_id v).const_sub 1) hv
  convert (hA.mul hB).sub (hasDerivAt_id v) using 1
  · rfl
  · dsimp [saddleSlopeDerivative]
    ring

/-- A fixed neighborhood whose state denominators stay uniformly positive. -/
def saddleSlopeRectangle (γ : ℝ) : Set (ℝ × ℝ) :=
  Icc (-(saddleU γ / 2)) (saddleU γ / 2) ×ˢ Icc 0 γ

theorem saddleSlope_denominators {γ : ℝ} (hγ₁ : γ < 1)
    {p : ℝ × ℝ} (hp : p ∈ saddleSlopeRectangle γ) :
    0 < saddleU γ - p.1 ∧ 0 < 1 - p.2 := by
  have hU := saddleU_pos hγ₁
  exact ⟨by linarith [hp.1.2], by linarith [hp.2.2]⟩

theorem saddleSlopeRate_continuousOn {γ : ℝ} (hγ₁ : γ < 1) :
    ContinuousOn (fun p : ℝ × ℝ ↦ saddleSlopeRate γ p.1 p.2) (saddleSlopeRectangle γ) := by
  unfold saddleSlopeRate
  have hd₁ (p : ℝ × ℝ) (hp : p ∈ saddleSlopeRectangle γ) : saddleU γ - p.1 ≠ 0 :=
    ne_of_gt (saddleSlope_denominators hγ₁ hp).1
  have hd₂ (p : ℝ × ℝ) (hp : p ∈ saddleSlopeRectangle γ) : 1 - p.2 ≠ 0 :=
    ne_of_gt (saddleSlope_denominators hγ₁ hp).2
  exact (((continuousOn_const.sub (continuous_snd.continuousOn.mul continuous_fst.continuousOn)).const_mul 2).div
    (continuousOn_const.sub continuous_fst.continuousOn) hd₁).mul
    ((continuousOn_const.sub continuous_snd.continuousOn).div
      (continuousOn_const.sub continuous_snd.continuousOn) hd₂) |>.sub continuous_snd.continuousOn

theorem saddleSlopeDerivative_continuousOn {γ : ℝ} (hγ₁ : γ < 1) :
    ContinuousOn (fun p : ℝ × ℝ ↦ saddleSlopeDerivative γ p.1 p.2) (saddleSlopeRectangle γ) := by
  unfold saddleSlopeDerivative
  have hd₁ (p : ℝ × ℝ) (hp : p ∈ saddleSlopeRectangle γ) : saddleU γ - p.1 ≠ 0 :=
    ne_of_gt (saddleSlope_denominators hγ₁ hp).1
  have hd₂ (p : ℝ × ℝ) (hp : p ∈ saddleSlopeRectangle γ) : 1 - p.2 ≠ 0 :=
    ne_of_gt (saddleSlope_denominators hγ₁ hp).2
  have hA : ContinuousOn (fun p : ℝ × ℝ ↦ 2 * (saddleS γ - p.2 * p.1) / (saddleU γ - p.1))
      (saddleSlopeRectangle γ) :=
    ((continuousOn_const.sub (continuous_snd.continuousOn.mul continuous_fst.continuousOn)).const_mul 2).div
      (continuousOn_const.sub continuous_fst.continuousOn) hd₁
  have hB : ContinuousOn (fun p : ℝ × ℝ ↦ (γ - p.2) / (1 - p.2)) (saddleSlopeRectangle γ) :=
    (continuousOn_const.sub continuous_snd.continuousOn).div
      (continuousOn_const.sub continuous_snd.continuousOn) hd₂
  exact (((continuous_fst.continuousOn.const_mul (-2)).div
    (continuousOn_const.sub continuous_fst.continuousOn) hd₁).mul hB).add
    (hA.mul (continuousOn_const.div ((continuousOn_const.sub continuous_snd.continuousOn).pow 2)
      (fun p hp ↦ pow_ne_zero _ (hd₂ p hp)))) |>.sub continuousOn_const

theorem saddleSlopeRate_uniform_bounds {γ : ℝ} (hγ₁ : γ < 1) :
    ∃ L K : ℝ≥0,
      (∀ z ∈ Icc (-(saddleU γ / 2)) (saddleU γ / 2),
        ∀ v ∈ Icc 0 γ, ‖saddleSlopeRate γ z v‖ ≤ L) ∧
      ∀ z ∈ Icc (-(saddleU γ / 2)) (saddleU γ / 2),
        LipschitzOnWith K (saddleSlopeRate γ z) (Icc 0 γ) :=
  exists_uniform_bounds_on_rectangle (saddleSlopeRate_continuousOn hγ₁)
    (saddleSlopeDerivative_continuousOn hγ₁)
    (fun z hz v hv ↦ saddleSlopeRate_hasDerivAt
      (ne_of_gt (saddleSlope_denominators hγ₁ (p := (z, v)) ⟨hz, hv⟩).2))

/-- Clip only the chord-slope coordinate. -/
def saddleSlopeClip (γ v : ℝ) : ℝ := max 0 (min v γ)

theorem saddleSlopeClip_mem {γ : ℝ} (hγ : 0 ≤ γ) (v : ℝ) :
    saddleSlopeClip γ v ∈ Icc 0 γ :=
  ⟨le_max_left _ _, max_le hγ (min_le_right _ _)⟩

theorem saddleSlopeClip_eq {γ v : ℝ} (hv : v ∈ Icc 0 γ) : saddleSlopeClip γ v = v := by
  simp [saddleSlopeClip, min_eq_left hv.2, max_eq_right hv.1]

theorem saddleSlopeClip_lipschitz (γ : ℝ) : LipschitzWith 1 (saddleSlopeClip γ) :=
  (LipschitzWith.id.min_const γ).const_max 0

theorem saddleSlopeRate_zero_pos {γ z : ℝ} (hγ : 0 < γ) (hγ₁ : γ < 1)
    (hz : z ∈ Icc (-(saddleU γ / 2)) (saddleU γ / 2)) :
    0 < saddleSlopeRate γ z 0 := by
  have hden := (saddleSlope_denominators hγ₁ (p := (z, 0)) ⟨hz, ⟨le_rfl, hγ.le⟩⟩).1
  simp only [saddleSlopeRate, zero_mul, sub_zero, div_one]
  exact mul_pos (div_pos (mul_pos (by norm_num) (saddleS_pos hγ hγ₁)) hden) hγ

theorem saddleSlopeRate_gamma (γ z : ℝ) : saddleSlopeRate γ z γ = -γ := by
  simp [saddleSlopeRate]

end
end krylov.LotkaVolterra
