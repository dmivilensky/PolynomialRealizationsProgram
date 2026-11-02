import krylov.LotkaVolterra.GlobalSaddleContraction
import krylov.LotkaVolterra.GlobalExpandingLimit
import Mathlib.Topology.Order.IntermediateValue

/-!
Article: `main_krylov`, `apC:prop:LV`, the stable tangent at the equilibrium.

There is exactly one admissible limiting chord slope. Every bounded slope
constructed by shooting converges to it. Thus the two signed branches have
the same tangent at the saddle; no limiting slope is postulated.

Source: intermediate value, strict scalar contraction, and the bounded
expanding-trajectory limit theorem of `GlobalExpandingLimit`.
-/
namespace krylov.LotkaVolterra
noncomputable section
open Set Filter
open scoped Topology

theorem exists_unique_saddle_tangent {γ : ℝ} (hγ : 0 < γ) (hγ₁ : γ < 1) :
    ∃! r : ℝ, r ∈ Ioo 0 γ ∧ saddleSlopeRate γ 0 r = 0 := by
  have hz : (0 : ℝ) ∈ Icc (-(saddleU γ / 2)) (saddleU γ / 2) := by
    have hh := saddleU_pos hγ₁
    constructor <;> linarith
  have hc : ContinuousOn (saddleSlopeRate γ 0) (Icc 0 γ) := by
    exact HasDerivAt.continuousOn fun v hv ↦ saddleSlopeRate_hasDerivAt
      (ne_of_gt (saddleSlope_denominators hγ₁ (p := (0, v)) ⟨hz, hv⟩).2)
  have h0 := saddleSlopeRate_zero_pos hγ hγ₁ hz
  obtain ⟨r, hr, hroot⟩ := intermediate_value_Icc' hγ.le hc
    (show (0 : ℝ) ∈ Icc (saddleSlopeRate γ 0 γ) (saddleSlopeRate γ 0 0) by
      rw [saddleSlopeRate_gamma]
      exact ⟨neg_nonpos.mpr hγ.le, h0.le⟩)
  have hrstrict : r ∈ Ioo 0 γ := by
    constructor
    · by_contra! hh
      have heq : r = 0 := le_antisymm hh hr.1
      rw [heq] at hroot
      linarith
    · by_contra! hh
      have heq : r = γ := le_antisymm hr.2 hh
      rw [heq, saddleSlopeRate_gamma] at hroot
      linarith
  refine ⟨r, ⟨hrstrict, hroot⟩, fun s hs ↦ ?_⟩
  have hh := saddleSlopeRate_expansion hγ hγ₁ hz hr
    (show s ∈ Icc 0 γ from ⟨hs.1.1.le, hs.1.2.le⟩)
  rw [hroot, hs.2] at hh
  nlinarith [sq_nonneg (r - s)]

theorem bounded_saddle_slope_tendsto {γ ε r : ℝ} (hγ : 0 < γ) (hγ₁ : γ < 1)
    (hε : |ε| ≤ 1) (hr : r ∈ Ioo 0 γ) (hroot : saddleSlopeRate γ 0 r = 0)
    {v : ℝ → ℝ}
    (hv : ∀ t ≥ 0, v t ∈ Icc 0 γ ∧ HasDerivAt v
      (-saddleSlopeRate γ (ε * (saddleU γ / 2) * Real.exp (-t)) (v t)) t) :
    Tendsto v atTop (𝓝 r) := by
  let F : ℝ → ℝ → ℝ := fun t v ↦
    -saddleSlopeRate γ (ε * (saddleU γ / 2) * Real.exp (-t)) v
  have hstrong (t : ℝ) (ht : 0 ≤ t) (x : ℝ) (hx : x ∈ Icc 0 γ)
      (y : ℝ) (hy : y ∈ Icc 0 γ) :
      (1 / 3 : ℝ) * (x - y) ^ 2 ≤ (x - y) * (F t x - F t y) := by
    have hz := saddleDistance_mem hγ₁ hε t
    simp only [saddleDistance, max_eq_right ht] at hz
    simpa [F, div_eq_mul_inv, sub_eq_add_neg, mul_comm] using
      saddleSlopeRate_expansion hγ hγ₁ hz hx hy
  have hzlim : Tendsto (fun t : ℝ ↦ ε * (saddleU γ / 2) * Real.exp (-t)) atTop (𝓝 0) := by
    simpa using (Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot).const_mul
      (ε * (saddleU γ / 2))
  have hc : ContinuousAt (fun z ↦ -saddleSlopeRate γ z r) 0 := by
    have hden : saddleU γ - (0 : ℝ) ≠ 0 := by
      simpa using ne_of_gt (saddleU_pos hγ₁)
    unfold saddleSlopeRate
    exact ((((continuousAt_const.sub (continuousAt_const.mul continuousAt_id)).const_mul 2).div
      (continuousAt_const.sub continuousAt_id) hden).mul continuousAt_const).sub continuousAt_const |>.neg
  have hres : Tendsto (fun t ↦ F t r) atTop (𝓝 0) := by
    simpa [F, hroot, Function.comp_def] using hc.tendsto.comp hzlim
  exact bounded_expanding_solution_tendsto (by norm_num : (0 : ℝ) < 1 / 3)
    ⟨hr.1.le, hr.2.le⟩ hstrong hres hv

theorem bounded_saddle_slope_unique {γ ε : ℝ} (hγ : 0 < γ) (hγ₁ : γ < 1)
    (hε : |ε| ≤ 1) {v w : ℝ → ℝ}
    (hv : ∀ t ≥ 0, v t ∈ Icc 0 γ ∧ HasDerivAt v
      (-saddleSlopeRate γ (ε * (saddleU γ / 2) * Real.exp (-t)) (v t)) t)
    (hw : ∀ t ≥ 0, w t ∈ Icc 0 γ ∧ HasDerivAt w
      (-saddleSlopeRate γ (ε * (saddleU γ / 2) * Real.exp (-t)) (w t)) t) :
    EqOn v w (Ici 0) := by
  apply bounded_expanding_solution_unique (by norm_num : (0 : ℝ) < 1 / 3)
    (F := fun t v ↦ -saddleSlopeRate γ (ε * (saddleU γ / 2) * Real.exp (-t)) v) ?_ hv hw
  intro t ht x hx y hy
  have hz := saddleDistance_mem hγ₁ hε t
  simp only [saddleDistance, max_eq_right ht] at hz
  simpa [div_eq_mul_inv, sub_eq_add_neg, mul_comm] using
    saddleSlopeRate_expansion hγ hγ₁ hz hx hy

end
end krylov.LotkaVolterra
