import polyak.Global.Circle.Phase

/-! Article lem:A-smooth for the actual convolution of arbitrary probability measures. -/
noncomputable section
namespace polyak.Global.Circle
open MeasureTheory Set Function Complex
open scoped Topology

variable {Φ:ℝ→ℝ} (hp:Periodic Φ (2*Real.pi)) (hc:Continuous Φ)
include hc

theorem averagedWave_integrable (n:ℤ) (ε:ℝ) (μ:Measure Circle) [IsFiniteMeasure μ] :
    Integrable (averagedWave Φ hp n ε) μ := by
  have hj : Integrable (fun p:Circle×ℝ=>wave Φ hp n (p.1+ofReal p.2))
      (μ.prod (Kernels.kernelMeasure ε)) := by
    apply (integrable_const (1:ℝ)).mono' (by
      exact ((wave_continuous hp hc n).comp (continuous_fst.add
        (continuous_ofReal.comp continuous_snd))).aestronglyMeasurable)
    exact ae_of_all _ fun x=>by rw [wave_norm]
  exact hj.integral_prod_left

theorem phaseMoment_smooth (n:ℤ) (ε:ℝ) (μ:Measure Circle) [IsFiniteMeasure μ] :
    phaseMoment Φ hp (smoothMeasure ε μ) n=∫x,averagedWave Φ hp n ε x∂μ := by
  unfold phaseMoment smoothMeasure
  rw [Measure.conv_comm,integral_conv (wave_integrable hp hc n _)]
  congr 1
  ext x
  rw [kernel,integral_map (f:=fun y:Circle=>wave Φ hp n (x+y)) continuous_ofReal.measurable.aemeasurable
    (((wave_continuous hp hc n).comp (continuous_const.add continuous_id)).aestronglyMeasurable)]
  rfl

theorem phaseMoment_smoothing_bound (dΦ:ℝ→ℝ) {M1 M2:ℝ}
    (hDerivative:∀v,|dΦ v|≤M1)
    (hTaylor:∀v t,|Φ (v+t)-Φ v-dΦ v*t|≤M2*t^2/2)
    (n:ℤ) (ε:ℝ) (μ:Measure Circle) [IsProbabilityMeasure μ] :
    ‖phaseMoment Φ hp (smoothMeasure ε μ) n-
      (Kernels.kernelHat ε n:ℂ)*phaseMoment Φ hp μ n‖≤
      M2*Kernels.mK*ε^2/2+Kernels.oscillation ε M1 n := by
  have hpoint (x:Circle) :
      ‖averagedWave Φ hp n ε x-(Kernels.kernelHat ε n:ℂ)*wave Φ hp n x‖≤
        M2*Kernels.mK*ε^2/2+Kernels.oscillation ε M1 n := by
    induction x using Quotient.inductionOn' with | h v =>
      change ‖averagedWave Φ hp n ε (ofReal v)-
        (Kernels.kernelHat ε n:ℂ)*wave Φ hp n (ofReal v)‖≤_
      rw [averagedWave_ofReal,wave_ofReal,mul_comm (Kernels.kernelHat ε n:ℂ)]
      exact Kernels.localAverage_constant Φ dΦ hc hDerivative hTaylor n ε v
  have hi := norm_integral_le_of_norm_le (μ:=μ)
    (integrable_const (M2*Kernels.mK*ε^2/2+Kernels.oscillation ε M1 n)) (ae_of_all _ hpoint)
  rw [integral_sub (averagedWave_integrable hp hc n ε μ)
    ((wave_integrable hp hc n μ).const_mul _),integral_const_mul,
    integral_const,probReal_univ,one_smul] at hi
  rw [phaseMoment_smooth hp hc]
  exact hi

/-- Literal source smoothing inequality. The sharper D₀+Dₙ estimate implies its D₀+3Dₙ form. -/
theorem smoothing_constraint (dΦ:ℝ→ℝ) {M1 M2:ℝ} (hM1:0≤M1)
    (hDerivative:∀v,|dΦ v|≤M1)
    (hTaylor:∀v t,|Φ (v+t)-Φ v-dΦ v*t|≤M2*t^2/2)
    (n:ℤ) (ε:ℝ) (μ:Measure Circle) [IsProbabilityMeasure μ] :
    Kernels.kernelHat ε n*phaseConstraint Φ hp μ n+
      (1-Kernels.kernelHat ε n)*phaseMinimizer Φ hp μ-
      Kernels.oscillation ε M1 0-3*Kernels.oscillation ε M1 n-M2*Kernels.mK*ε^2≤
      phaseConstraint Φ hp (smoothMeasure ε μ) n := by
  have h₀ := phaseMoment_smoothing_bound hp hc dΦ hDerivative hTaylor 0 ε μ
  have hₙ := phaseMoment_smoothing_bound hp hc dΦ hDerivative hTaylor n ε μ
  have hr₀ := (Complex.abs_re_le_norm _).trans h₀
  have hrₙ := (Complex.abs_re_le_norm _).trans hₙ
  simp only [Complex.sub_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero,Kernels.kernelHat_zero,Int.cast_zero,one_mul] at hr₀ hrₙ
  have hD := Kernels.oscillation_nonneg hM1 ε (n:ℝ)
  dsimp [phaseConstraint,phaseMinimizer]
  linarith [(abs_le.mp hr₀).1,(abs_le.mp hrₙ).2]

/-- The minimizer moment retains the exact half-Taylor-error bound. -/
theorem smoothing_minimizer (dΦ:ℝ→ℝ) {M1 M2:ℝ}
    (hDerivative:∀v,|dΦ v|≤M1)
    (hTaylor:∀v t,|Φ (v+t)-Φ v-dΦ v*t|≤M2*t^2/2)
    (ε:ℝ) (μ:Measure Circle) [IsProbabilityMeasure μ] :
    phaseMinimizer Φ hp μ-Kernels.oscillation ε M1 0-M2*Kernels.mK*ε^2/2≤
      phaseMinimizer Φ hp (smoothMeasure ε μ) := by
  have h₀ := phaseMoment_smoothing_bound hp hc dΦ hDerivative hTaylor 0 ε μ
  have hr₀ := (Complex.abs_re_le_norm _).trans h₀
  simp only [Complex.sub_re,Kernels.kernelHat_zero,Int.cast_zero,Complex.ofReal_one,one_mul] at hr₀
  dsimp [phaseMinimizer]
  linarith [(abs_le.mp hr₀).1]

end polyak.Global.Circle
