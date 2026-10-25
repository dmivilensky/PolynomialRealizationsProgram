import polyak.Global.Kernels.Fourier
import polyak.Global.Kernels.Moments

/-! The real cosine transforms are the literal source Fourier coefficients. -/
noncomputable section
namespace polyak.Global.Kernels
open MeasureTheory Set Function Complex
open scoped Topology ENNReal NNReal

theorem exp_integrable (μ:Measure ℝ) [IsFiniteMeasure μ] (ξ:ℝ) :
    Integrable (fun x:ℝ=>Complex.exp ((ξ*x:ℝ)*Complex.I)) μ := by
  apply (integrable_const (1:ℝ)).mono' (by fun_prop)
  filter_upwards with x
  rw [Complex.norm_exp_ofReal_mul_I]

theorem cos_integrable (μ:Measure ℝ) [IsFiniteMeasure μ] (ξ:ℝ) :
    Integrable (fun x:ℝ=>Real.cos (ξ*x)) μ := by
  apply (integrable_const (1:ℝ)).mono' (by fun_prop)
  exact ae_of_all _ fun _=>Real.abs_cos_le_one _

theorem real_charFun_integral_cos (μ:Measure ℝ) [IsFiniteMeasure μ] (ξ:ℝ) :
    (charFun μ ξ).re=∫x,Real.cos (ξ*x)∂μ := by
  rw [charFun_apply_real]
  have hi := integral_re (exp_integrable μ ξ)
  change (∫x,(Complex.exp ((ξ*x:ℝ)*Complex.I)).re∂μ)=
    (∫x,Complex.exp ((ξ*x:ℝ)*Complex.I)∂μ).re at hi
  simp_rw [Complex.exp_ofReal_mul_I_re] at hi
  simpa only [Complex.ofReal_mul] using hi.symm

theorem psiHat_integral_cos (ξ:ℝ) : psiHat ξ=∫x,Real.cos (ξ*x)∂psiMeasure :=
  real_charFun_integral_cos _ _

theorem phiHat_integral_cos (ξ:ℝ) : phiHat ξ=∫x,Real.cos (ξ*x)∂phiMeasure := by
  have hh := real_charFun_integral_cos phiMeasure ξ
  rw [phi_characteristic,Complex.ofReal_re] at hh
  exact hh

theorem kernelHat_integral_cos (ε ξ:ℝ) : kernelHat ε ξ=∫x,Real.cos (ξ*x)∂kernelMeasure ε := by
  have hh := real_charFun_integral_cos (kernelMeasure ε) ξ
  rw [kernel_characteristic,Complex.ofReal_re] at hh
  exact hh

end polyak.Global.Kernels
