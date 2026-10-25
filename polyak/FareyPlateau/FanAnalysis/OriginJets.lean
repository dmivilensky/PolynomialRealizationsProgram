import polyak.FareyPlateau.FanAnalysis.ActualJets

/-! First-order pinning constraints at the grid points immediately on either
side of zero. -/
noncomputable section
namespace polyak.FareyPlateau.FanAnalysis
open Filter
open scoped Topology

theorem linear_limit {f : ℝ → ℝ} (hf : AnalyticAt ℝ f 0) (hf0 : f 0 = 0) :
    Tendsto (fun δ => f δ/δ) (𝓝[≠] 0) (𝓝 (deriv f 0)) := by
  have hh := hf.differentiableAt.hasDerivAt.tendsto_slope
  change Tendsto (fun δ => slope f 0 δ) _ _ at hh
  simpa only [slope_def_field, hf0, sub_zero] using hh

namespace Actual
open General Levels ModeLocking
variable {q : Tuning} {j k : ℕ} (A : Edge.AdjacentData q j k)

theorem near_origin_limit (e y : ℝ) :
    Tendsto (fun δ => lagPath 0 y (nearAngle A e) δ/δ) (𝓝[≠] 0)
      (𝓝 (-Real.sin (Real.pi / k)*y)) := by
  have hh := linear_limit (analyticAt_lagPath (near_analytic A e) 0 y)
    (zero_lag_value (near_value A e) y)
  rw [zero_lag_first (near_analytic A e) (near_value A e)] at hh
  exact hh

theorem far_origin_limit (e y : ℝ) :
    Tendsto (fun δ => lagPath 0 y (farAngle A e) δ/δ) (𝓝[≠] 0)
      (𝓝 (-Real.sin (Real.pi / k)*y)) := by
  have hh := linear_limit (analyticAt_lagPath (far_analytic A e) 0 y)
    (zero_lag_value (far_value A e) y)
  rw [zero_lag_first (far_analytic A e) (far_value A e)] at hh
  exact hh

end Actual
end polyak.FareyPlateau.FanAnalysis
