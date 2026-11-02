import krylov.LotkaVolterra.GlobalSaddleLimit
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
Article: `main_krylov`, `apC:prop:LV`, continuous chord-slope graph through
the equilibrium. Signed distances are normalized by `c = U_F/2`, so the
graph parameter ranges over `[-1,1]`.

The two actual shooting solutions are joined at their common limiting
slope. This produces a continuous graph through the saddle satisfying its
exact singular differential equation off the saddle. Analyticity through
the saddle remains a distinct regularity assertion.
-/
namespace krylov.LotkaVolterra
noncomputable section
open Set Filter
open scoped Topology

/-- Join the signed shooting slopes, using logarithmic distance as time. -/
def joinedSaddleSlope (vminus vplus : ℝ → ℝ) (r u : ℝ) : ℝ :=
  if u = 0 then r else if u < 0 then vminus (-Real.log u) else vplus (-Real.log u)

theorem joinedSaddleSlope_zero (vminus vplus : ℝ → ℝ) (r : ℝ) :
    joinedSaddleSlope vminus vplus r 0 = r := by simp [joinedSaddleSlope]

theorem joinedSaddleSlope_continuousAt_zero {vminus vplus : ℝ → ℝ} {r : ℝ}
    (hm : Tendsto vminus atTop (𝓝 r)) (hp : Tendsto vplus atTop (𝓝 r)) :
    ContinuousAt (joinedSaddleSlope vminus vplus r) 0 := by
  rw [continuousAt_iff_punctured_nhds, joinedSaddleSlope_zero]
  have hq : Tendsto (fun u : ℝ ↦ -Real.log u) (𝓝[≠] 0) atTop :=
    tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsNE_zero
  apply tendsto_def.mpr
  intro S hS
  filter_upwards [(hm.comp hq).eventually hS, (hp.comp hq).eventually hS,
    self_mem_nhdsWithin] with u hum hup hu
  have hu₀ : u ≠ 0 := hu
  change (if u = 0 then r else if u < 0 then vminus (-Real.log u) else vplus (-Real.log u)) ∈ S
  rw [ite_eq_right hu₀]
  split_ifs <;> assumption

theorem neg_log_nonneg_of_abs_le_one {u : ℝ} (hu : u ≠ 0) (hu₁ : |u| ≤ 1) :
    0 ≤ -Real.log u := by
  have hh := Real.log_le_log (abs_pos.mpr hu) hu₁
  rw [Real.log_abs, Real.log_one] at hh
  linarith

theorem joinedSaddleSlope_hasDerivAt {γ r u : ℝ} {vm vp : ℝ → ℝ}
    (hu : u ≠ 0) (hu₁ : |u| ≤ 1)
    (hm : ∀ t ≥ 0, HasDerivAt vm
      (-saddleSlopeRate γ (-1 * (saddleU γ / 2) * Real.exp (-t)) (vm t)) t)
    (hp : ∀ t ≥ 0, HasDerivAt vp
      (-saddleSlopeRate γ (1 * (saddleU γ / 2) * Real.exp (-t)) (vp t)) t) :
    HasDerivAt (joinedSaddleSlope vm vp r)
      (saddleSlopeRate γ ((saddleU γ / 2) * u) (joinedSaddleSlope vm vp r u) / u) u := by
  have hq := neg_log_nonneg_of_abs_le_one hu hu₁
  have hlog : HasDerivAt (fun u : ℝ ↦ -Real.log u) (-(1 / u)) u := by
    convert (Real.hasDerivAt_log hu).neg using 1
    simp only [one_div]
  rcases lt_or_gt_of_ne hu with hun | hup
  · have hdist : -1 * (saddleU γ / 2) * Real.exp (-(-Real.log u)) = (saddleU γ / 2) * u := by
      rw [neg_neg, Real.exp_log_eq_abs hu, abs_of_neg hun]
      ring
    have hd := (hm _ hq).comp u hlog
    rw [hdist] at hd
    have heq : joinedSaddleSlope vm vp r =ᶠ[𝓝 u] fun u ↦ vm (-Real.log u) := by
      filter_upwards [Iio_mem_nhds hun] with z hz
      change z < 0 at hz
      simp [joinedSaddleSlope, ne_of_lt hz, hz]
    have hval : joinedSaddleSlope vm vp r u = vm (-Real.log u) := by
      simp [joinedSaddleSlope, hu, hun]
    rw [hval]
    convert hd.congr_of_eventuallyEq heq using 1
    ring
  · have hdist : 1 * (saddleU γ / 2) * Real.exp (-(-Real.log u)) = (saddleU γ / 2) * u := by
      rw [neg_neg, Real.exp_log_eq_abs hu, abs_of_pos hup]
      ring
    have hd := (hp _ hq).comp u hlog
    rw [hdist] at hd
    have heq : joinedSaddleSlope vm vp r =ᶠ[𝓝 u] fun u ↦ vp (-Real.log u) := by
      filter_upwards [Ioi_mem_nhds hup] with z hz
      change 0 < z at hz
      simp [joinedSaddleSlope, ne_of_gt hz, not_lt.mpr hz.le]
    have hval : joinedSaddleSlope vm vp r u = vp (-Real.log u) := by
      simp [joinedSaddleSlope, hu, not_lt.mpr hup.le]
    rw [hval]
    convert hd.congr_of_eventuallyEq heq using 1
    ring

/-- An unconditional continuous chord graph through the saddle, with its
exact invariance equation away from zero. This is the concrete input for
analytic regularity at the regular-singular point. -/
theorem exists_continuous_saddle_chord {γ : ℝ} (hγ : 0 < γ) (hγ₁ : γ < 1) :
    ∃ r : ℝ, ∃ w : ℝ → ℝ,
      r ∈ Ioo 0 γ ∧ saddleSlopeRate γ 0 r = 0 ∧ w 0 = r ∧
      ContinuousAt w 0 ∧ ContinuousOn w (Icc (-1 : ℝ) 1) ∧
      ∀ u ∈ Icc (-1 : ℝ) 1, w u ∈ Ioo 0 γ ∧
        (u ≠ 0 → HasDerivAt w (saddleSlopeRate γ ((saddleU γ / 2) * u) (w u) / u) u) := by
  obtain ⟨r, ⟨hr, hroot⟩, _⟩ := exists_unique_saddle_tangent hγ hγ₁
  obtain ⟨vm, hm⟩ := exists_bounded_saddle_slope hγ hγ₁ (ε := -1) (by norm_num)
  obtain ⟨vp, hp⟩ := exists_bounded_saddle_slope hγ hγ₁ (ε := 1) (by norm_num)
  let w := joinedSaddleSlope vm vp r
  have hc : ContinuousAt w 0 := joinedSaddleSlope_continuousAt_zero
    (bounded_saddle_slope_tendsto hγ hγ₁ (by norm_num) hr hroot hm)
    (bounded_saddle_slope_tendsto hγ hγ₁ (by norm_num) hr hroot hp)
  have hd {u : ℝ} (hu₁ : |u| ≤ 1) (hu : u ≠ 0) :
      HasDerivAt w (saddleSlopeRate γ ((saddleU γ / 2) * u) (w u) / u) u :=
    joinedSaddleSlope_hasDerivAt hu hu₁ (fun t ht ↦ (hm t ht).2) (fun t ht ↦ (hp t ht).2)
  refine ⟨r, w, hr, hroot, joinedSaddleSlope_zero _ _ _, hc, ?_, fun u hu ↦ ?_⟩
  · intro u hu
    by_cases hu₀ : u = 0
    · subst u
      exact hc.continuousWithinAt
    · exact (hd (abs_le.mpr hu) hu₀).continuousAt.continuousWithinAt
  · by_cases hu₀ : u = 0
    · subst u
      exact ⟨by simpa [w, joinedSaddleSlope] using hr, fun h ↦ (h rfl).elim⟩
    · have hq := neg_log_nonneg_of_abs_le_one hu₀ (abs_le.mpr hu)
      refine ⟨?_, hd (abs_le.mpr hu)⟩
      rcases lt_or_gt_of_ne hu₀ with hun | hup
      · simpa [w, joinedSaddleSlope, hu₀, hun] using
          bounded_saddle_slope_strict hγ hγ₁ (by norm_num) hm hq
      · simpa [w, joinedSaddleSlope, hu₀, not_lt.mpr hup.le] using
          bounded_saddle_slope_strict hγ hγ₁ (by norm_num) hp hq

end
end krylov.LotkaVolterra
