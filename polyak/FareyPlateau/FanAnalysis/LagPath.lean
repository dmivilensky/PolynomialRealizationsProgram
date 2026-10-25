import polyak.FareyPlateau.FanAnalysis.JetCalculus

/-! Exact jets for constraints at a linearly moving phase-grid point. -/
noncomputable section
namespace polyak.FareyPlateau.FanAnalysis
open Filter
open scoped Topology

def lagPath (τ y : ℝ) (f : ℝ → ℝ) (δ : ℝ) : ℝ :=
  Real.cos (f δ) - Real.cos (τ + y * δ - f δ)

theorem analyticAt_lagPath {f : ℝ → ℝ} (hf : AnalyticAt ℝ f 0) (τ y : ℝ) :
    AnalyticAt ℝ (lagPath τ y f) 0 :=
  (Real.analyticAt_cos.comp hf).sub
    (Real.analyticAt_cos.comp ((analyticAt_const.add (analyticAt_const.mul analyticAt_id)).sub hf))

theorem argument_first {f : ℝ → ℝ} (hf : AnalyticAt ℝ f 0) (τ y : ℝ) :
    deriv (fun δ => τ + y * δ - f δ) 0 = y - deriv f 0 := by
  have ha := (((hasDerivAt_id (0 : ℝ)).const_mul y).const_add τ).sub hf.differentiableAt.hasDerivAt
  convert ha.deriv using 1 <;> simp only [Pi.sub_def, id_eq, mul_one]

theorem argument_second {f : ℝ → ℝ} (hf : AnalyticAt ℝ f 0) (τ y : ℝ) :
    deriv^[2] (fun δ => τ + y * δ - f δ) 0 = -deriv^[2] f 0 := by
  have he : deriv (fun δ => τ + y * δ - f δ) =ᶠ[𝓝 0] fun δ => y - deriv f δ := by
    filter_upwards [hf.eventually_analyticAt] with δ hδ
    have ha := (((hasDerivAt_id δ).const_mul y).const_add τ).sub hδ.differentiableAt.hasDerivAt
    convert ha.deriv using 1 <;> simp only [Pi.sub_def, id_eq, mul_one]
  change deriv (deriv (fun δ => τ + y * δ - f δ)) 0 = -deriv (deriv f) 0
  rw [he.deriv_eq]
  exact (hf.deriv.differentiableAt.hasDerivAt.const_sub y).deriv

theorem lagPath_first {f : ℝ → ℝ} (hf : AnalyticAt ℝ f 0) (τ y : ℝ) :
    deriv (lagPath τ y f) 0 = -Real.sin (f 0) * deriv f 0 +
      Real.sin (τ - f 0) * (y - deriv f 0) := by
  have ha := (((hasDerivAt_id (0 : ℝ)).const_mul y).const_add τ).sub hf.differentiableAt.hasDerivAt
  have hd := hf.differentiableAt.hasDerivAt.cos.sub ha.cos
  convert hd.deriv using 1
  · rfl
  · simp only [Pi.sub_apply, id_eq, mul_one, mul_zero, add_zero]
    ring

theorem lagPath_second {f : ℝ → ℝ} (hf : AnalyticAt ℝ f 0) (τ y : ℝ) :
    deriv^[2] (lagPath τ y f) 0 = -Real.cos (f 0) * (deriv f 0)^2 -
      (Real.sin (f 0) + Real.sin (τ - f 0)) * deriv^[2] f 0 +
      Real.cos (τ - f 0) * (y - deriv f 0)^2 := by
  have ha : AnalyticAt ℝ (fun δ => τ + y * δ - f δ) 0 :=
    (analyticAt_const.add (analyticAt_const.mul analyticAt_id)).sub hf
  have hh : iteratedDeriv 2 (lagPath τ y f) 0 =
      iteratedDeriv 2 (fun δ => Real.cos (f δ)) 0 -
      iteratedDeriv 2 (fun δ => Real.cos (τ + y * δ - f δ)) 0 :=
    iteratedDeriv_fun_sub ((Real.analyticAt_cos.comp hf).contDiffAt : ContDiffAt ℝ 2 (fun δ : ℝ => Real.cos (f δ)) (0 : ℝ))
      ((Real.analyticAt_cos.comp ha).contDiffAt : ContDiffAt ℝ 2 (fun δ : ℝ => Real.cos (τ + y * δ - f δ)) (0 : ℝ))
  simp only [iteratedDeriv_eq_iterate] at hh
  rw [hh, cos_second hf, cos_second ha, argument_first hf τ y, argument_second hf τ y]
  simp only [mul_zero, add_zero]
  ring

end polyak.FareyPlateau.FanAnalysis
