import polyak.Global.Circle.SmoothConvolutionRegularity
import polyak.Global.Circle.SmoothConvolutionMeasure
import polyak.Global.Circle.PeriodizationKernel

/-! The actual source kernel produces a genuine C∞ even probability density. -/
noncomputable section
namespace polyak.Global.Circle
open MeasureTheory Set Function
open scoped Topology ContDiff ENNReal NNReal

def smoothDensity (ε:ℝ) (μ:Measure Circle) : Circle→ℝ := convolutionDensity (kernelDensity ε) μ

theorem continuous_smoothDensity {ε:ℝ} (hε:0<ε)
    (μ:Measure Circle) [IsFiniteMeasure μ] : Continuous (smoothDensity ε μ) :=
  continuous_convolutionDensity (continuous_kernelDensity hε) μ

theorem smoothDensity_nonneg {ε:ℝ} (hε:0<ε) (μ:Measure Circle) (x:Circle) :
    0≤smoothDensity ε μ x := convolutionDensity_nonneg (kernelDensity_nonneg hε) μ x

theorem smoothDensity_even {ε:ℝ} (hε:0<ε) {μ:Measure Circle} [IsFiniteMeasure μ]
    (hμ:Symmetric μ) (x:Circle) : smoothDensity ε μ (-x)=smoothDensity ε μ x :=
  convolutionDensity_even (continuous_kernelDensity hε) (kernelDensity_even ε) hμ x

theorem smooth_smoothDensity {ε:ℝ} (hε:0<ε)
    (μ:Measure Circle) [IsFiniteMeasure μ] :
    ContDiff ℝ ∞ (fun x=>smoothDensity ε μ (ofReal x)) :=
  smooth_convolutionDensity (smooth_kernelDensity_lift hε) μ

theorem smoothDensity_periodic (ε:ℝ) (μ:Measure Circle) :
    Periodic (fun x=>smoothDensity ε μ (ofReal x)) (2*Real.pi) :=
  realPullback_periodic _

theorem smoothDensity_measure {ε:ℝ} (hε:0<ε) (hεπ:ε<Real.pi)
    (μ:Measure Circle) [IsFiniteMeasure μ] :
    smoothMeasure ε μ=haar.withDensity (fun x=>ENNReal.ofReal (smoothDensity ε μ x)) := by
  rw [smoothMeasure,kernelCircle_density hε hεπ]
  exact convolutionDensity_measure (continuous_kernelDensity hε) (kernelDensity_nonneg hε) μ

theorem integral_smoothDensity {ε:ℝ} (hε:0<ε) (hεπ:ε<Real.pi)
    (μ:Measure Circle) [IsProbabilityMeasure μ] : ∫x,smoothDensity ε μ x∂haar=1 := by
  have hi : Integrable (smoothDensity ε μ) haar :=
    (continuous_smoothDensity hε μ).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hh : ENNReal.ofReal (∫x,smoothDensity ε μ x∂haar)=1 := by
    rw [ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ (smoothDensity_nonneg hε μ))]
    calc
      _ = (haar.withDensity (fun x=>ENNReal.ofReal (smoothDensity ε μ x))) univ := by
        rw [withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ]
      _ = 1 := by rw [←smoothDensity_measure hε hεπ μ];exact measure_univ
  exact ENNReal.ofReal_eq_one.mp hh

end polyak.Global.Circle
