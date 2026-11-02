import krylov.LotkaVolterra.GlobalSaddleChord
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
Article: `main_krylov`, `apC:prop:LV`, weighted Volterra form of the actual
continuous chord equation at the saddle.

The identity is an application of the ordinary fundamental theorem of
calculus to `t^a (w(zt)-r)`. The power has an integrable derivative because
`a>0`; continuity and `w(0)=r` handle the endpoint. Thus no improper
integration or boundary term is assumed.

Source: the classical Briot--Bouquet weighted integral equation and
mathlib's interval fundamental theorem of calculus / real-power integrability.
-/
namespace krylov.LotkaVolterra
noncomputable section
open Set MeasureTheory

/-- Weighted integral identity for a continuous regular-singular chord
solution. All hypotheses concern the actual constructed chord; no analytic
solution is supplied as an assumption. -/
theorem saddle_chord_weighted_identity
    {H : ℝ → ℝ → ℝ} {w : ℝ → ℝ} {c r a z : ℝ}
    (ha : 0 < a) (hw₀ : w 0 = r) (hroot : H 0 r = 0)
    (hw : ContinuousOn w (Icc (-1 : ℝ) 1))
    (hd : ∀ u ∈ Icc (-1 : ℝ) 1, u ≠ 0 → HasDerivAt w (H (c * u) (w u) / u) u)
    (hz : |z| ≤ 1)
    (hN : ContinuousOn (fun t : ℝ ↦ H (c * z * t) (w (z * t)) + a * (w (z * t) - r))
      (Icc 0 1)) :
    w z - r = ∫ t in Ioc (0 : ℝ) 1,
      t ^ (a - 1) * (H (c * z * t) (w (z * t)) + a * (w (z * t) - r)) := by
  by_cases hz₀ : z = 0
  · simp [hz₀, hw₀, hroot]
  have hmap {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : z * t ∈ Icc (-1 : ℝ) 1 := by
    have habs : |z * t| ≤ 1 := by
      rw [abs_mul, abs_of_nonneg ht.1]
      exact (mul_le_mul_of_nonneg_right hz ht.1).trans (by simpa using ht.2)
    exact abs_le.mp habs
  let V : ℝ → ℝ := fun t ↦ t ^ a * (w (z * t) - r)
  let N : ℝ → ℝ := fun t ↦ H (c * z * t) (w (z * t)) + a * (w (z * t) - r)
  have hV : ContinuousOn V (Icc (0 : ℝ) 1) := by
    exact (continuousOn_id.rpow_const (fun _ _ ↦ Or.inr ha.le)).mul
      ((hw.comp (continuousOn_const.mul continuousOn_id) (fun _ ht ↦ hmap ht)).sub continuousOn_const)
  have hder (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
      HasDerivAt V (t ^ (a - 1) * N t) t := by
    have ht₀ : t ≠ 0 := ne_of_gt ht.1
    have hzt : z * t ≠ 0 := mul_ne_zero hz₀ ht₀
    have hwt := (hd (z * t) (hmap (Ioo_subset_Icc_self ht)) hzt).comp t
      ((hasDerivAt_id t).const_mul z)
    have hh := (Real.hasDerivAt_rpow_const (Or.inl ht₀) (p := a)).mul (hwt.sub_const r)
    simp only [Function.comp_apply, mul_one] at hh
    have hid : (a * t ^ (a - 1)) * (w (z * t) - r) +
        t ^ a * (H (c * (z * t)) (w (z * t)) / (z * t) * z) = t ^ (a - 1) * N t := by
      dsimp [N]
      rw [Real.rpow_sub_one ht₀ a]
      field_simp
      ring
    rw [hid] at hh
    exact hh
  have hint : IntervalIntegrable (fun t : ℝ ↦ t ^ (a - 1) * N t) volume 0 1 :=
    (intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < a - 1)).mul_continuousOn
      (by simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hN)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (by norm_num : (0 : ℝ) ≤ 1) hV hder hint
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hFTC
  simpa [V, N, hw₀] using hFTC.symm

/-- The actual saddle field satisfies the continuity hypothesis of the
weighted identity on every contraction of the constructed physical chord. -/
theorem actual_saddle_chord_weighted_identity {γ a r : ℝ} {w : ℝ → ℝ}
    (hγ₁ : γ < 1) (ha : 0 < a) (hw₀ : w 0 = r) (hroot : saddleSlopeRate γ 0 r = 0)
    (hw : ContinuousOn w (Icc (-1 : ℝ) 1))
    (hwstrip : ∀ u ∈ Icc (-1 : ℝ) 1, w u ∈ Icc 0 γ)
    (hd : ∀ u ∈ Icc (-1 : ℝ) 1, u ≠ 0 →
      HasDerivAt w (saddleSlopeRate γ ((saddleU γ / 2) * u) (w u) / u) u)
    {z : ℝ} (hz : |z| ≤ 1) :
    w z - r = ∫ t in Ioc (0 : ℝ) 1,
      t ^ (a - 1) * (saddleSlopeRate γ ((saddleU γ / 2) * z * t) (w (z * t)) +
        a * (w (z * t) - r)) := by
  have hmap {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : z * t ∈ Icc (-1 : ℝ) 1 := by
    apply abs_le.mp
    rw [abs_mul, abs_of_nonneg ht.1]
    exact (mul_le_mul_of_nonneg_right hz ht.1).trans (by simpa using ht.2)
  have hW : ContinuousOn (fun t : ℝ ↦ w (z * t)) (Icc 0 1) :=
    hw.comp (continuousOn_const.mul continuousOn_id) (fun _ ht ↦ hmap ht)
  have hP : ContinuousOn (fun t : ℝ ↦ ((saddleU γ / 2) * z * t, w (z * t))) (Icc 0 1) :=
    (continuousOn_const.mul continuousOn_id).prodMk hW
  have hrect : MapsTo (fun t : ℝ ↦ ((saddleU γ / 2) * z * t, w (z * t)))
      (Icc 0 1) (saddleSlopeRectangle γ) := by
    intro t ht
    have hzt := hmap ht
    have hc : 0 ≤ saddleU γ / 2 := (half_pos (saddleU_pos hγ₁)).le
    have hlo := mul_le_mul_of_nonneg_left hzt.1 hc
    have hhi := mul_le_mul_of_nonneg_left hzt.2 hc
    refine ⟨⟨?_, ?_⟩, hwstrip _ hzt⟩
    · nlinarith
    · nlinarith
  exact saddle_chord_weighted_identity ha hw₀ hroot hw hd hz
    (((saddleSlopeRate_continuousOn hγ₁).comp hP hrect).add
      (continuousOn_const.mul (hW.sub continuousOn_const)))

end
end krylov.LotkaVolterra
