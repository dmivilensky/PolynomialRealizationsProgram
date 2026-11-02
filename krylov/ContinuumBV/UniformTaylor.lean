import krylov.ContinuumBV.TaylorSums
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.UniformSpace.Compact

/-!
Article: main_krylov, apC:lem:fund, uniform Taylor control.
Use: derive the vanishing derivative-oscillation estimates from genuine C¹
regularity on a compact convex state domain, with no assumed Taylor modulus.
Source: Heine–Cantor on the actual derivative and convex-segment geometry.
-/

namespace krylov.ContinuumBV
noncomputable section
open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Compact C¹ regularity supplies one uniform state tolerance controlling
the derivative along every sufficiently short chord of the state domain. -/
theorem exists_uniform_derivative_oscillation {F : E → ℝ} {s : Set E}
    (hc : IsCompact s) (hs : Convex ℝ s) (hF : ∀ w ∈ s, ContDiffAt ℝ 1 F w)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > (0 : ℝ), ∀ x ∈ s, ∀ y ∈ s, ‖y - x‖ < δ →
      ∀ w ∈ segment ℝ x y, ‖fderiv ℝ F w - fderiv ℝ F x‖ ≤ ε := by
  have hD : ContinuousOn (fderiv ℝ F) s := fun w hw =>
    ((hF w hw).continuousAt_fderiv (by norm_num)).continuousWithinAt
  obtain ⟨δ, hδ, hosc⟩ := Metric.uniformContinuousOn_iff.1
    (hc.uniformContinuousOn_of_continuous hD) ε hε
  refine ⟨δ, hδ, ?_⟩
  intro x hx y hy hxy w hw
  have hws := hs.segment_subset hx hy hw
  have hwx : dist w x < δ := by
    rw [dist_eq_norm]
    exact (norm_sub_le_of_mem_segment hw).trans_lt hxy
  simpa only [dist_eq_norm] using (hosc w hws x hx hwx).le

/-- The resulting uniform first-order Taylor estimate is an actual theorem
of C¹ calculus on the compact domain, rather than an extra certificate field. -/
theorem exists_uniform_taylor_remainder {F : E → ℝ} {s : Set E}
    (hc : IsCompact s) (hs : Convex ℝ s) (hF : ∀ w ∈ s, ContDiffAt ℝ 1 F w)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > (0 : ℝ), ∀ x ∈ s, ∀ y ∈ s, ‖y - x‖ < δ →
      ‖F y - F x - fderiv ℝ F x (y - x)‖ ≤ ε * ‖y - x‖ := by
  obtain ⟨δ, hδ, hosc⟩ := exists_uniform_derivative_oscillation hc hs hF hε
  refine ⟨δ, hδ, ?_⟩
  intro x hx y hy hxy
  exact taylor_remainder_le
    (fun w hw => ((hF w (hs.segment_subset hx hy hw)).differentiableAt (by norm_num)).hasFDerivAt)
    (hosc x hx y hy hxy)

/-- Compact localization removes convexity of the state domain. A C¹
potential near its actual compact state range has one uniform tolerance on
all short chords, including the points of those chords outside the range. -/
theorem exists_uniform_local_taylor_data {F : E → ℝ} {s : Set E}
    (hc : IsCompact s) (hF : ∀ w ∈ s, ContDiffAt ℝ 1 F w)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > (0 : ℝ), ∀ x ∈ s, ∀ y, ‖y - x‖ < δ →
      ∀ w ∈ segment ℝ x y,
        HasFDerivAt F (fderiv ℝ F w) w ∧ ‖fderiv ℝ F w - fderiv ℝ F x‖ ≤ ε := by
  let U : Set E := {w | ContDiffAt ℝ 1 F w}
  have hU : IsOpen U := by
    apply isOpen_iff_mem_nhds.2
    intro w hw
    change ContDiffAt ℝ 1 F w at hw
    exact hw.eventually (by norm_num)
  obtain ⟨V, hV, _hVo, hVU⟩ := lebesgue_number_of_compact_open hc hU hF
  obtain ⟨δ₀, hδ₀, hVδ⟩ := Metric.mem_uniformity_dist.1 hV
  have hderiv := hc.uniformContinuousAt_of_continuousAt (fderiv ℝ F)
    (fun w hw => (hF w hw).continuousAt_fderiv (by norm_num)) (Metric.dist_mem_uniformity hε)
  obtain ⟨δ₁, hδ₁, hDδ⟩ := Metric.mem_uniformity_dist.1 hderiv
  refine ⟨min δ₀ δ₁, lt_min hδ₀ hδ₁, ?_⟩
  intro x hx y hxy w hw
  have hd : dist x w < min δ₀ δ₁ := by
    rw [dist_comm, dist_eq_norm]
    exact (norm_sub_le_of_mem_segment hw).trans_lt hxy
  have hwU : w ∈ U := hVU x hx (hVδ (hd.trans_le (min_le_left _ _)))
  change ContDiffAt ℝ 1 F w at hwU
  have hbound : dist (fderiv ℝ F x) (fderiv ℝ F w) < ε :=
    hDδ (hd.trans_le (min_le_right _ _)) hx
  refine ⟨(hwU.differentiableAt (by norm_num)).hasFDerivAt, ?_⟩
  rw [← dist_eq_norm, dist_comm]
  exact hbound.le

end
end krylov.ContinuumBV
