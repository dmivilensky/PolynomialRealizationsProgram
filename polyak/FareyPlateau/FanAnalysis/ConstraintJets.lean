import polyak.FareyPlateau.FanAnalysis.LagPath
import polyak.FareyPlateau.Fan.Lattice

/-! Exact second-order constraints at every fixed scaled grid site.
Global grid control is obtained separately by convexity in the phase variable. -/
noncomputable section
namespace polyak.FareyPlateau.FanAnalysis
open Filter
open scoped Topology

def scaledConstraint (m z τ y : ℝ) (a c : ℝ → ℝ) (δ : ℝ) : ℝ :=
  (m + z * δ) * lagPath τ y a δ + lagPath (-m * τ) (-m * y) c δ

theorem analyticAt_scaledConstraint {a c : ℝ → ℝ}
    (ha : AnalyticAt ℝ a 0) (hc : AnalyticAt ℝ c 0) (m z τ y : ℝ) :
    AnalyticAt ℝ (scaledConstraint m z τ y a c) 0 :=
  (((analyticAt_const.add (analyticAt_const.mul analyticAt_id)).mul
    (analyticAt_lagPath ha τ y)).add (analyticAt_lagPath hc (-m * τ) (-m * y)))

theorem scaledConstraint_first {a c : ℝ → ℝ}
    (ha : AnalyticAt ℝ a 0) (hc : AnalyticAt ℝ c 0) (m z τ y : ℝ) :
    deriv (scaledConstraint m z τ y a c) 0 =
      z * lagPath τ y a 0 + m * deriv (lagPath τ y a) 0 +
        deriv (lagPath (-m * τ) (-m * y) c) 0 := by
  have hla := (analyticAt_lagPath ha τ y).differentiableAt.hasDerivAt
  have hlc := (analyticAt_lagPath hc (-m * τ) (-m * y)).differentiableAt.hasDerivAt
  have hw := (((hasDerivAt_id (0 : ℝ)).const_mul z).const_add m)
  have hd := (hw.mul hla).add hlc
  unfold scaledConstraint
  convert hd.deriv using 1 <;> simp only [Pi.add_def, Pi.mul_def, id_eq, mul_one, mul_zero, add_zero]

theorem scaledConstraint_second {a c : ℝ → ℝ}
    (ha : AnalyticAt ℝ a 0) (hc : AnalyticAt ℝ c 0) (m z τ y : ℝ) :
    deriv^[2] (scaledConstraint m z τ y a c) 0 =
      m * deriv^[2] (lagPath τ y a) 0 + 2 * z * deriv (lagPath τ y a) 0 +
        deriv^[2] (lagPath (-m * τ) (-m * y) c) 0 := by
  have hf := analyticAt_lagPath ha τ y
  have hg := analyticAt_lagPath hc (-m * τ) (-m * y)
  have hw : AnalyticAt ℝ (fun δ : ℝ => (m + z * δ) * lagPath τ y a δ) 0 :=
    (analyticAt_const.add (analyticAt_const.mul analyticAt_id)).mul hf
  have hh : iteratedDeriv 2 (scaledConstraint m z τ y a c) 0 =
      iteratedDeriv 2 (fun δ => (m + z * δ) * lagPath τ y a δ) 0 +
        iteratedDeriv 2 (lagPath (-m * τ) (-m * y) c) 0 :=
    iteratedDeriv_fun_add (hw.contDiffAt : ContDiffAt ℝ 2 _ (0 : ℝ))
      (hg.contDiffAt : ContDiffAt ℝ 2 _ (0 : ℝ))
  simp only [iteratedDeriv_eq_iterate] at hh
  rw [hh, weighted_second hf]
  simp only [mul_zero, add_zero]

theorem zero_lag_value {f : ℝ → ℝ} {c : ℝ} (hf : f 0 = c) (y : ℝ) : lagPath 0 y f 0 = 0 := by
  simp only [lagPath, hf, mul_zero, add_zero, zero_sub, Real.cos_neg, sub_self]

theorem zero_lag_first {f : ℝ → ℝ} {c : ℝ} (ha : AnalyticAt ℝ f 0) (hf : f 0 = c) (y : ℝ) :
    deriv (lagPath 0 y f) 0 = -Real.sin c * y := by
  rw [lagPath_first ha, hf]
  simp only [zero_sub, Real.sin_neg]
  ring

theorem zero_lag_second {f : ℝ → ℝ} {c : ℝ} (ha : AnalyticAt ℝ f 0) (hf : f 0 = c) (y : ℝ) :
    deriv^[2] (lagPath 0 y f) 0 = Real.cos c * y * (y - 2 * deriv f 0) := by
  rw [lagPath_second ha, hf]
  simp only [zero_sub, Real.cos_neg, Real.sin_neg]
  ring

theorem zero_constraint_limit {a c : ℝ → ℝ} {c₀ m z d : ℝ}
    (ha : AnalyticAt ℝ a 0) (hc : AnalyticAt ℝ c 0)
    (ha0 : a 0 = c₀) (hc0 : c 0 = c₀) (ha1 : deriv a 0 = d) (hc1 : deriv c 0 = -m * d) (y : ℝ) :
    Tendsto (fun δ => scaledConstraint m z 0 y a c δ / (2 * δ^2)) (𝓝[≠] 0)
      (𝓝 (m * (m + 1) * Real.cos c₀ / 4 * (y^2 - 2 * d * y) - Real.sin c₀ / 2 * z * y)) := by
  have hzero : scaledConstraint m z 0 y a c 0 = 0 := by
    simp only [scaledConstraint, neg_mul, mul_zero, zero_lag_value ha0, zero_lag_value hc0, mul_zero, add_zero]
  have hfirst : deriv (scaledConstraint m z 0 y a c) 0 = 0 := by
    rw [scaledConstraint_first ha hc]
    simp only [mul_zero, zero_lag_value ha0, zero_lag_first ha ha0, zero_lag_first hc hc0]
    ring
  have hsecond := scaledConstraint_second ha hc m z 0 y
  simp only [mul_zero, zero_lag_first ha ha0, zero_lag_second ha ha0,
    zero_lag_second hc hc0, ha1, hc1] at hsecond
  have hlim := quadratic_limit (analyticAt_scaledConstraint ha hc m z 0 y) hzero hfirst
  rw [hsecond] at hlim
  convert hlim using 1
  congr 1
  ring

theorem edge_lag_value {f : ℝ → ℝ} {c τ : ℝ} (hf : f 0 = c)
    (hcos : Real.cos (τ - c) = Real.cos c) (y : ℝ) : lagPath τ y f 0 = 0 := by
  simp only [lagPath, hf, mul_zero, add_zero, hcos, sub_self]

theorem edge_lag_first {f : ℝ → ℝ} {c τ : ℝ} (ha : AnalyticAt ℝ f 0) (hf : f 0 = c)
    (hsin : Real.sin (τ - c) = Real.sin c) (y : ℝ) :
    deriv (lagPath τ y f) 0 = Real.sin c * (y - 2 * deriv f 0) := by
  rw [lagPath_first ha, hf, hsin]
  ring

theorem edge_lag_second {f : ℝ → ℝ} {c τ : ℝ} (ha : AnalyticAt ℝ f 0) (hf : f 0 = c)
    (hsin : Real.sin (τ - c) = Real.sin c) (hcos : Real.cos (τ - c) = Real.cos c) (y : ℝ) :
    deriv^[2] (lagPath τ y f) 0 = Real.cos c * y * (y - 2 * deriv f 0) - 2 * Real.sin c * deriv^[2] f 0 := by
  rw [lagPath_second ha, hf, hsin, hcos]
  ring

theorem edge_constraint_limit {a c : ℝ → ℝ} {c₀ m z d d₂ e τ : ℝ}
    (ha : AnalyticAt ℝ a 0) (hc : AnalyticAt ℝ c 0)
    (ha0 : a 0 = c₀) (hc0 : c 0 = c₀) (ha1 : deriv a 0 = d) (hc1 : deriv c 0 = -m * d)
    (ha2 : deriv^[2] a 0 = d₂ + 2 * e * (Real.sin c₀)^2)
    (hc2 : deriv^[2] c 0 = m^2 * d₂ + 2 * e * (Real.sin c₀)^2)
    (hsin : Real.sin (τ - c₀) = Real.sin c₀) (hcos : Real.cos (τ - c₀) = Real.cos c₀)
    (hsinc : Real.sin (-m * τ - c₀) = Real.sin c₀) (hcosc : Real.cos (-m * τ - c₀) = Real.cos c₀)
    (y : ℝ) :
    Tendsto (fun δ => scaledConstraint m z τ y a c δ / (2 * δ^2)) (𝓝[≠] 0)
      (𝓝 (Fan.quadratic (m * (m + 1) * Real.cos c₀ / 4) (Real.sin c₀ / 2)
        ((m + 1) * m * d₂ + 2 * (m + 1) * (Real.sin c₀)^2 * e) (2 * d) z y)) := by
  have hzero : scaledConstraint m z τ y a c 0 = 0 := by
    simp only [scaledConstraint, mul_zero, add_zero, edge_lag_value ha0 hcos, edge_lag_value hc0 hcosc]
  have hfirst : deriv (scaledConstraint m z τ y a c) 0 = 0 := by
    rw [scaledConstraint_first ha hc]
    simp only [edge_lag_value ha0 hcos, mul_zero, zero_add, edge_lag_first ha ha0 hsin,
      edge_lag_first hc hc0 hsinc, ha1, hc1]
    ring
  have hsecond := scaledConstraint_second ha hc m z τ y
  rw [edge_lag_first ha ha0 hsin, edge_lag_second ha ha0 hsin hcos,
    edge_lag_second hc hc0 hsinc hcosc, ha1, hc1, ha2, hc2] at hsecond
  have hlim := quadratic_limit (analyticAt_scaledConstraint ha hc m z τ y) hzero hfirst
  rw [hsecond] at hlim
  convert hlim using 1
  congr 1
  unfold Fan.quadratic
  ring

end polyak.FareyPlateau.FanAnalysis
