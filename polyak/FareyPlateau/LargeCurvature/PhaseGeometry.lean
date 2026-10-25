import polyak.FareyPlateau.LargeCurvature.ZoneC
import polyak.ModeLocking.TwoLag.Extension
import polyak.ModeLocking.Analysis.JetBounds

noncomputable section
namespace polyak.FareyPlateau.LargeCurvature
open General Levels Set Filter
open scoped Topology BigOperators
namespace SourceData
variable {q : Tuning} {j k : ℕ} (B : SourceData q j k)
include B

omit B in
theorem phase_eq (_B : SourceData q j k) {x : ℝ} (hx : x ∈ Icc (0:ℝ) Real.pi) :
    ModeLocking.TwoLag.phase q 0 x=Geometry.shiftedAngle q 0 x := Geometry.jointAngle_actual q 0 hx

theorem phase_actual {x : ℝ} (hx : x ∈ Icc (0:ℝ) Real.pi) :
    ModeLocking.TwoLag.phase q 0 x=q.angle x := by
  rw [B.phase_eq hx]
  have hh := congrArg (fun C : Curve=>C ⟨x,hx.1,hx.2⟩) (Geometry.shiftedCurve_zero q)
  exact hh

theorem phase_actual_eventually {x : ℝ} (hx : x ∈ Ioo (0:ℝ) Real.pi) :
    ModeLocking.TwoLag.phase q 0 =ᶠ[𝓝 x] Geometry.shiftedAngle q 0 := by
  filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
  exact B.phase_eq ⟨hy.1.le,hy.2.le⟩

theorem center_phase : ModeLocking.TwoLag.phase q 0 B.ω=B.c := by
  rw [B.phase_actual ⟨B.ω_mem.1.le,B.ω_mem.2.le⟩]
  exact source_edge_phase q (by have := B.numerator_ge; omega) B.numerator_lt B.coefficients

theorem center_slope : 2*deriv (ModeLocking.TwoLag.phase q 0) B.ω=B.bar := by
  rw [(B.phase_actual_eventually B.ω_mem).deriv_eq]
  exact Ray.source_slope_index q (by have := B.numerator_ge; omega) B.numerator_lt B.coefficients

theorem center_below : B.ω ∈ Geometry.phaseBelow q 0 := by
  refine ⟨B.ω_mem,?_⟩
  rw [←B.phase_eq ⟨B.ω_mem.1.le,B.ω_mem.2.le⟩,B.center_phase]
  change Real.pi/k ≤ Real.pi/2
  exact div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num) (by have := B.kr; linarith)

theorem below_in_window {x : ℝ} (hx : x ∈ Geometry.phaseBelow q 0) : x ∈ B.window := by
  by_contra hn
  have hX := B.far_profile ⟨hx.1.1.le,hx.1.2.le⟩ hn
  have hcot := (Geometry.shiftedAngle_le_half_pi_iff q 0 hx.1).mp hx.2
  have hs := Real.sin_pos_of_pos_of_lt_pi hx.1.1 hx.1.2
  have hnonneg : 0 ≤ q.Xi (Real.cos x) := by
    simpa only [Geometry.cotangent,add_zero,div_mul_cancel₀ _ hs.ne'] using (mul_nonneg hcot hs.le)
  have hp : 0 < B.a*B.ε^2 := mul_pos B.a_pos (sq_pos_of_pos B.epsilon_pos)
  linarith

theorem second_lower {x : ℝ} (hx : x ∈ Geometry.phaseBelow q 0) :
    B.a*sineMargin k/centralFactor k B.h ≤ deriv^[2] (ModeLocking.TwoLag.phase q 0) x := by
  rw [←iteratedDeriv_eq_iterate,(B.phase_actual_eventually hx.1).iteratedDeriv_eq 2,iteratedDeriv_eq_iterate]
  exact phase_second_lower q B.coefficients B.h_nonneg B.max_nonneg B.asymmetry_bound
    (a1_faces B.large).2.2.1.le B.a_pos (sineMargin_pos B.kr) hx.1
    (central_sine_lower B.kr B.N_ge B.ω_lower B.ω_upper (B.below_in_window hx)) hx.2

end SourceData
end polyak.FareyPlateau.LargeCurvature
