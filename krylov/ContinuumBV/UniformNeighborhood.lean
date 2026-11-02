import krylov.ContinuumBV.UniformTaylor

/-!
Article: main_krylov, apC:lem:fund, localization near admissible states.
Use: compact C¹ regularity provides one genuine neighborhood on which the
derivative exists and remains bounded, even outside the invariant state set.
Source: the compact Lebesgue number lemma and compact derivative continuity.
-/

namespace krylov.ContinuumBV
noncomputable section
open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A compact C¹ domain has one uniform C¹ neighborhood and a bounded
derivative there. Convexity of the domain is unnecessary. -/
theorem exists_uniform_contDiff_neighborhood {F : E → ℝ} {s : Set E}
    (hc : IsCompact s) (hF : ∀ w ∈ s, ContDiffAt ℝ 1 F w) :
    ∃ δ > (0 : ℝ), ∃ C, ∀ x ∈ s, ∀ y, ‖y - x‖ < δ →
      ContDiffAt ℝ 1 F y ∧ ‖fderiv ℝ F y‖ ≤ C := by
  let U : Set E := {w | ContDiffAt ℝ 1 F w}
  have hU : IsOpen U := by
    apply isOpen_iff_mem_nhds.2
    intro w hw
    change ContDiffAt ℝ 1 F w at hw
    exact hw.eventually (by norm_num)
  obtain ⟨V, hV, _hVo, hVU⟩ := lebesgue_number_of_compact_open hc hU hF
  obtain ⟨δ₀, hδ₀, hVδ⟩ := Metric.mem_uniformity_dist.1 hV
  obtain ⟨C, hC⟩ := hc.exists_bound_of_continuousOn (f := fderiv ℝ F)
    (fun w hw => ((hF w hw).continuousAt_fderiv (by norm_num)).continuousWithinAt)
  have hderiv := hc.uniformContinuousAt_of_continuousAt (fderiv ℝ F)
    (fun w hw => (hF w hw).continuousAt_fderiv (by norm_num))
      (Metric.dist_mem_uniformity (by norm_num : (0 : ℝ) < 1))
  obtain ⟨δ₁, hδ₁, hDδ⟩ := Metric.mem_uniformity_dist.1 hderiv
  refine ⟨min δ₀ δ₁, lt_min hδ₀ hδ₁, C + 1, ?_⟩
  intro x hx y hxy
  have hd : dist x y < min δ₀ δ₁ := by simpa only [dist_eq_norm, norm_sub_rev] using hxy
  have hy : y ∈ U := hVU x hx (hVδ (hd.trans_le (min_le_left _ _)))
  refine ⟨hy, ?_⟩
  have hdiff : ‖fderiv ℝ F y - fderiv ℝ F x‖ < 1 := by
    have hd' : dist (fderiv ℝ F x) (fderiv ℝ F y) < 1 :=
      hDδ (hd.trans_le (min_le_right _ _)) hx
    simpa only [dist_eq_norm, norm_sub_rev] using hd'
  calc
    _ ≤ ‖fderiv ℝ F y - fderiv ℝ F x‖ + ‖fderiv ℝ F x‖ := norm_le_norm_sub_add _ _
    _ ≤ C + 1 := by linarith [hC x hx]

end
end krylov.ContinuumBV
