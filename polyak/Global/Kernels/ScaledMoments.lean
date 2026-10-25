import polyak.Global.Kernels.HatIntegral

/-! Exact scaled second moment of the actual source probability kernel. -/
noncomputable section
namespace polyak.Global.Kernels
open MeasureTheory Set Function

theorem kernelMeasure_integrable_square (ε:ℝ) : Integrable (fun x:ℝ=>x^2) (kernelMeasure ε) := by
  apply (integrable_map_measure (by fun_prop) (by fun_prop)).mpr
  simpa only [Function.comp_def,mul_pow] using (kappaMeasure_integrable_pow 2).const_mul (ε^2)

theorem kernelMeasure_second_moment (ε:ℝ) : ∫x:ℝ,x^2∂kernelMeasure ε=ε^2*mK := by
  rw [kernelMeasure,integral_map (by fun_prop) (by fun_prop)]
  simp only [mul_pow]
  rw [integral_const_mul]
  rfl

end polyak.Global.Kernels
