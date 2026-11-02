import krylov.LotkaVolterra.GlobalSaddleShooting
import krylov.LotkaVolterra.GlobalEndpointGraph

/-!
Article: `main_krylov`, `apC:prop:LV`, actual stable branches near the saddle.

The bounded slopes from compact shooting give nonconstant curves converging
to the interior equilibrium. Their tangents are the exact LV field after
a strictly positive time change. This is a construction of the geometric
stable branches, not an assumption of a stable manifold. Analytic extension
through the equilibrium is a separate regularity step.

Source: the logarithmic-distance substitution and compact scalar shooting.
-/
namespace krylov.LotkaVolterra
noncomputable section
open Set Filter
open scoped Topology

theorem bounded_saddle_slope_strict {γ ε : ℝ} (hγ : 0 < γ) (hγ₁ : γ < 1)
    (hε : |ε| ≤ 1) {v : ℝ → ℝ}
    (hv : ∀ t ≥ 0, v t ∈ Icc 0 γ ∧ HasDerivAt v
      (-saddleSlopeRate γ (ε * (saddleU γ / 2) * Real.exp (-t)) (v t)) t)
    {t : ℝ} (ht : 0 ≤ t) : v t ∈ Ioo 0 γ := by
  have h := hv t ht
  constructor
  · by_contra! hle
    have heq : v t = 0 := le_antisymm hle h.1.1
    have hd := derivative_nonneg_of_right_lower_bound h.2
      (fun T hT ↦ by rw [heq]; exact (hv T (ht.trans hT.le)).1.1)
    rw [heq] at hd
    have hz := saddleDistance_mem hγ₁ hε t
    simp only [saddleDistance, max_eq_right ht] at hz
    exact (not_le_of_gt (saddleSlopeRate_zero_pos hγ hγ₁ hz)) (neg_nonneg.mp hd)
  · by_contra! hle
    have heq : v t = γ := le_antisymm h.1.2 hle
    have hd := derivative_nonpos_of_right_upper_bound h.2
      (fun T hT ↦ by rw [heq]; exact (hv T (ht.trans hT.le)).1.2)
    rw [heq, saddleSlopeRate_gamma, neg_neg] at hd
    exact (not_le_of_gt hγ) hd

theorem saddleSlopeRate_tangent {γ z v : ℝ} (hU : saddleU γ - z ≠ 0)
    (hv : 1 - v ≠ 0) :
    (saddleU γ - z) * (1 - v) * (v + saddleSlopeRate γ z v) =
      2 * (saddleS γ - v * z) * (γ - v) := by
  unfold saddleSlopeRate
  field_simp
  ring

/-- Both geometric stable branches are constructed with their exact LV
tangent equation and a strictly positive time change. Their distance from
the saddle is explicit, so convergence does not depend on an assumed
stable-manifold theorem. -/
theorem exists_stable_saddle_branch {γ ε : ℝ} (hγ : 0 < γ) (hγ₁ : γ < 1)
    (hε : |ε| ≤ 1) :
    ∃ v : ℝ → ℝ, ∃ α α' : ℝ → ℝ × ℝ,
      Tendsto α atTop (𝓝 (saddlePoint γ)) ∧
      ∀ t ≥ 0, v t ∈ Ioo 0 γ ∧
        α t = (saddleS γ - v t * (ε * (saddleU γ / 2) * Real.exp (-t)),
          saddleU γ - ε * (saddleU γ / 2) * Real.exp (-t)) ∧
        α t ∈ positiveQuadrant ∧ HasDerivAt α (α' t) t ∧
        0 < (α t).2 * (1 - v t) ∧
        ((α t).2 * (1 - v t)) • α' t = vectorField γ (α t) := by
  obtain ⟨v, hv⟩ := exists_bounded_saddle_slope hγ hγ₁ hε
  let z : ℝ → ℝ := fun t ↦ ε * (saddleU γ / 2) * Real.exp (-t)
  let α : ℝ → ℝ × ℝ := fun t ↦ (saddleS γ - v t * z t, saddleU γ - z t)
  let α' : ℝ → ℝ × ℝ := fun t ↦ (z t * (v t + saddleSlopeRate γ (z t) (v t)), z t)
  have hzlim : Tendsto z atTop (𝓝 0) := by
    have hh := (Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot).const_mul
      (ε * (saddleU γ / 2))
    simpa [z] using hh
  have hvzlim : Tendsto (fun t ↦ v t * z t) atTop (𝓝 0) := by
    have hbound : ∀ᶠ t in atTop, ‖v t * z t‖ ≤ γ * ‖z t‖ := by
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hv t ht).1.1]
      exact mul_le_mul_of_nonneg_right (hv t ht).1.2 (norm_nonneg _)
    exact squeeze_zero_norm' hbound (by simpa using hzlim.norm.const_mul γ)
  have hαlim : Tendsto α atTop (𝓝 (saddlePoint γ)) := by
    simpa [α, saddlePoint] using
      ((tendsto_const_nhds (x := saddleS γ)).sub hvzlim).prodMk_nhds
        ((tendsto_const_nhds (x := saddleU γ)).sub hzlim)
  refine ⟨v, α, α', hαlim, fun t ht ↦ ?_⟩
  have hvstrict := bounded_saddle_slope_strict hγ hγ₁ hε hv ht
  have hzmem := saddleDistance_mem hγ₁ hε t
  simp only [saddleDistance, max_eq_right ht] at hzmem
  change z t ∈ Icc _ _ at hzmem
  have hUpos : 0 < saddleU γ - z t :=
    (saddleSlope_denominators hγ₁ (p := (z t, v t)) ⟨hzmem, (hv t ht).1⟩).1
  have hvpos : 0 < 1 - v t := by linarith [hvstrict.2]
  have hspos : 0 < saddleS γ - v t * z t := by
    have hU := saddleU_pos hγ₁
    have hs := saddleS_eq_one_add_mul_saddleU (ne_of_lt hγ₁)
    have hh := mul_le_mul_of_nonneg_left hzmem.2 (hv t ht).1.1
    have hh' := mul_le_mul_of_nonneg_right (hv t ht).1.2 (half_pos hU).le
    nlinarith
  have hzder : HasDerivAt z (-z t) t := by
    simpa [z] using ((hasDerivAt_id t).neg.exp.const_mul (ε * (saddleU γ / 2)))
  have hSder := (((hv t ht).2).mul hzder).const_sub (saddleS γ)
  have hUder := hzder.const_sub (saddleU γ)
  have hder : HasDerivAt α (α' t) t := by
    convert hSder.prodMk hUder using 1
    apply Prod.ext <;> dsimp [α'] <;> ring
  refine ⟨hvstrict, rfl, ⟨hspos, hUpos⟩, hder, mul_pos hUpos hvpos, ?_⟩
  have htan := saddleSlopeRate_tangent (ne_of_gt hUpos) (ne_of_gt hvpos)
  have hs := saddleS_eq_one_add_mul_saddleU (ne_of_lt hγ₁)
  have hU := saddleU_eq_saddleS_add_one (ne_of_lt hγ₁)
  apply Prod.ext
  · change (saddleU γ - z t) * (1 - v t) *
      (z t * (v t + saddleSlopeRate γ (z t) (v t))) = _
    calc
      _ = z t * ((saddleU γ - z t) * (1 - v t) *
          (v t + saddleSlopeRate γ (z t) (v t))) := by ring
      _ = z t * (2 * (saddleS γ - v t * z t) * (γ - v t)) := by rw [htan]
      _ = _ := by dsimp [vectorField, sRate, α]; rw [hs]; ring
  · dsimp [α, α', vectorField, uRate]
    rw [hU]
    ring

end
end krylov.LotkaVolterra
