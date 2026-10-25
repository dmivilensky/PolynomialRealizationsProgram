import polyak.FareyPlateau.FanAnalysis.FiniteTests

/-! A fixed adjacent dual certificate has a double zero along each atom path.
Its quadratic coefficient gives the necessary fan bound without assuming any
rate of convergence for the two masses. -/
noncomputable section
namespace polyak.FareyPlateau.FanAnalysis
open Filter
open scoped Topology

theorem linear_second {f g : ℝ → ℝ} (hf : AnalyticAt ℝ f 0)
    (hg : AnalyticAt ℝ g 0) (a b : ℝ) :
    deriv^[2] (fun x => a * f x + b * g x) 0 =
      a * deriv^[2] f 0 + b * deriv^[2] g 0 := by
  have ha : AnalyticAt ℝ (fun x => a*f x) 0 := analyticAt_const.mul hf
  have hb : AnalyticAt ℝ (fun x => b*g x) 0 := analyticAt_const.mul hg
  rw [← iteratedDeriv_eq_iterate]
  rw [iteratedDeriv_fun_add (ha.contDiffAt : ContDiffAt ℝ 2 _ (0 : ℝ))
    (hb.contDiffAt : ContDiffAt ℝ 2 _ (0 : ℝ)),
    iteratedDeriv_const_mul_field, iteratedDeriv_const_mul_field]
  simp only [iteratedDeriv_eq_iterate]

namespace Actual
open General Levels ModeLocking
variable {q : Tuning} {j k : ℕ} (A : Edge.AdjacentData q j k)

def dualPath (f : ℝ → ℝ) (h δ : ℝ) : ℝ :=
  (1 - A.mix) * lagPath ((A.lower : ℝ) * A.frequency) ((A.lower : ℝ) * h) f δ +
    A.mix * lagPath ((A.upper : ℝ) * A.frequency) ((A.upper : ℝ) * h) f δ

theorem dualPath_analytic {f : ℝ → ℝ} (hf : AnalyticAt ℝ f 0) (h : ℝ) :
    AnalyticAt ℝ (dualPath A f h) 0 :=
  (analyticAt_const.mul (analyticAt_lagPath hf _ _)).add (analyticAt_const.mul (analyticAt_lagPath hf _ _))

theorem dualPath_zero {f : ℝ → ℝ} (hf0 : f 0 = Real.pi / k) (h : ℝ) :
    dualPath A f h 0 = 0 := by
  have ht₁ := (A.lag_trig A.lower (by simp [Edge.AdjacentData.lags])).2
  have ht₂ := (A.lag_trig A.upper (by simp [Edge.AdjacentData.lags])).2
  rw [A.phase_value] at ht₁ ht₂
  simp only [dualPath, lagPath, hf0, mul_zero, add_zero, ht₁, ht₂, sub_self,
    mul_zero, add_zero]

theorem dualPath_first {f : ℝ → ℝ} (hf : AnalyticAt ℝ f 0)
    (hf0 : f 0 = Real.pi / k) {h : ℝ} (hf1 : deriv f 0 = h * first A) :
    deriv (dualPath A f h) 0 = 0 := by
  have hl₁ := analyticAt_lagPath hf ((A.lower : ℝ) * A.frequency) ((A.lower : ℝ) * h)
  have hl₂ := analyticAt_lagPath hf ((A.upper : ℝ) * A.frequency) ((A.upper : ℝ) * h)
  have hs₁ := (A.lag_trig A.lower (by simp [Edge.AdjacentData.lags])).1
  have hs₂ := (A.lag_trig A.upper (by simp [Edge.AdjacentData.lags])).1
  rw [A.phase_value] at hs₁ hs₂
  unfold dualPath
  rw [deriv_fun_add (hl₁.differentiableAt.const_mul _) (hl₂.differentiableAt.const_mul _),
    deriv_const_mul_field, deriv_const_mul_field,
    edge_lag_first hf hf0 hs₁, edge_lag_first hf hf0 hs₂, hf1]
  have hslope := slope A
  simp only [Edge.AdjacentData.upper, Int.cast_add, Int.cast_natCast]
  have hfval : first A = ((A.lower : ℝ) + A.mix*k)/2 := by linarith
  rw [hfval]
  ring

theorem dualPath_second {f : ℝ → ℝ} (hf : AnalyticAt ℝ f 0)
    (hf0 : f 0 = Real.pi / k) {h e : ℝ}
    (hf1 : deriv f 0 = h * first A)
    (hf2 : deriv^[2] f 0 = h^2 * second A + 2 * e * (Real.sin (Real.pi / k))^2) :
    deriv^[2] (dualPath A f h) 0 =
      -2 * h^2 * deriv^[2] A.function A.frequency - 4 * e * (Real.sin (Real.pi / k))^3 := by
  have ht₁ := A.lag_trig A.lower (by simp [Edge.AdjacentData.lags])
  have ht₂ := A.lag_trig A.upper (by simp [Edge.AdjacentData.lags])
  rw [A.phase_value] at ht₁ ht₂
  unfold dualPath
  rw [linear_second (analyticAt_lagPath hf _ _) (analyticAt_lagPath hf _ _),
    edge_lag_second hf hf0 ht₁.1 ht₁.2, edge_lag_second hf hf0 ht₂.1 ht₂.2,
    hf1, hf2, A.second, ← second_actual A]
  have hslope := slope A
  simp only [Edge.AdjacentData.upper, Int.cast_add, Int.cast_natCast]
  have hfval : first A = ((A.lower : ℝ) + A.mix*k)/2 := by linarith
  rw [hfval]
  ring

theorem dualPath_limit {f : ℝ → ℝ} (hf : AnalyticAt ℝ f 0)
    (hf0 : f 0 = Real.pi / k) {h e : ℝ}
    (hf1 : deriv f 0 = h * first A)
    (hf2 : deriv^[2] f 0 = h^2 * second A + 2 * e * (Real.sin (Real.pi / k))^2) :
    Tendsto (fun δ => dualPath A f h δ / δ^2) (𝓝[≠] 0)
      (𝓝 (-h^2 * deriv^[2] A.function A.frequency - 2 * e * (Real.sin (Real.pi / k))^3)) := by
  have hh := (quadratic_limit (dualPath_analytic A hf h) (dualPath_zero A hf0 h)
    (dualPath_first A hf hf0 hf1)).mul_const 2
  rw [dualPath_second A hf hf0 hf1 hf2] at hh
  convert hh using 1
  · ext δ
    ring
  · ring

theorem near_dual_limit (e : ℝ) :
    Tendsto (fun δ => dualPath A (nearAngle A e) 1 δ / δ^2) (𝓝[≠] 0)
      (𝓝 (-deriv^[2] A.function A.frequency - 2 * e * (Real.sin (Real.pi / k))^3)) := by
  simpa only [one_pow, one_mul, neg_mul, one_mul] using dualPath_limit A (h := 1) (e := e) (near_analytic A e)
    (near_value A e) (by simpa only [one_mul] using near_first A e)
    (by simpa only [one_pow, one_mul] using near_second A e)

theorem far_dual_limit (e : ℝ) :
    Tendsto (fun δ => dualPath A (farAngle A e) (-((k : ℝ) - 1)) δ / δ^2) (𝓝[≠] 0)
      (𝓝 (-((k : ℝ) - 1)^2 * deriv^[2] A.function A.frequency - 2 * e * (Real.sin (Real.pi / k))^3)) := by
  simpa only [neg_sq] using dualPath_limit A (h := -((k : ℝ) - 1)) (e := e) (far_analytic A e)
    (far_value A e) (far_first A e)
    (by simpa only [neg_sq] using far_second A e)

end Actual
end polyak.FareyPlateau.FanAnalysis
