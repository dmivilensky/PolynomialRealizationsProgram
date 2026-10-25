import polyak.FareyPlateau.Edge.Jets
import polyak.ModeLocking.Localization.Taylor

/-! Actual second jets and quadratic limits used in the signed fan problem.
The calculus identities apply to genuine analytic functions. -/
noncomputable section
namespace polyak.FareyPlateau.FanAnalysis
open Filter
open scoped Topology

theorem cos_second {f : ℝ → ℝ} {x : ℝ} (hf : AnalyticAt ℝ f x) :
    deriv^[2] (fun y => Real.cos (f y)) x =
      -Real.cos (f x) * (deriv f x)^2 - Real.sin (f x) * deriv^[2] f x := by
  have he : deriv (fun y => Real.cos (f y)) =ᶠ[𝓝 x]
      fun y => -Real.sin (f y) * deriv f y := by
    filter_upwards [hf.eventually_analyticAt] with y hy
    exact hy.differentiableAt.hasDerivAt.cos.deriv
  have hd := (hf.differentiableAt.hasDerivAt.sin.neg).mul hf.deriv.differentiableAt.hasDerivAt
  change deriv (deriv (fun y => Real.cos (f y))) x = _
  rw [he.deriv_eq]
  convert hd.deriv using 1
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply, Pi.neg_apply]
  ring

theorem weighted_second {f : ℝ → ℝ} {m z x : ℝ} (hf : AnalyticAt ℝ f x) :
    deriv^[2] (fun y => (m + z * y) * f y) x =
      (m + z * x) * deriv^[2] f x + 2 * z * deriv f x := by
  have ha : AnalyticAt ℝ (fun y : ℝ => m + z * y) x := by fun_prop
  have hh := iteratedDeriv_fun_mul (ha.contDiffAt : ContDiffAt ℝ 2 _ x)
    (hf.contDiffAt : ContDiffAt ℝ 2 _ x)
  have hlin : deriv (fun y : ℝ => m + z * y) = fun _ => z := by
    funext y
    simpa only [id_eq, mul_one] using (((hasDerivAt_id y).const_mul z).const_add m).deriv
  have hlin2 : deriv^[2] (fun y : ℝ => m + z * y) x = 0 := by
    change deriv (deriv (fun y : ℝ => m + z * y)) x = 0
    rw [hlin]
    exact deriv_const _ _
  norm_num [Finset.sum_range_succ, iteratedDeriv_zero, iteratedDeriv_one,
    iteratedDeriv_eq_iterate, hlin, hlin2] at hh
  change deriv (deriv (fun y => (m + z * y) * f y)) x =
    (m + z * x) * deriv (deriv f) x + 2 * z * deriv f x
  exact hh

theorem quadratic_limit {f : ℝ → ℝ} (hf : AnalyticAt ℝ f 0)
    (hzero : f 0 = 0) (hfirst : deriv f 0 = 0) :
    Tendsto (fun δ => f δ / (2 * δ^2)) (𝓝[≠] 0) (𝓝 (deriv^[2] f 0 / 4)) := by
  have hh := ModeLocking.Localization.analytic_quadratic_limit hf hzero hfirst
  have hlim := hh.div_const 2
  convert hlim using 1
  · ext δ
    simp only [sub_zero]
    ring
  · congr 1
    change deriv (deriv f) 0 / 4 = _
    ring

end polyak.FareyPlateau.FanAnalysis
