import polyak.Global.Circle.Probability
import polyak.Global.Circle.Kernel
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! Actual convolution densities for finite circle measures. -/
noncomputable section
namespace polyak.Global.Circle
open MeasureTheory Set Function
open scoped Topology ENNReal NNReal

def convolutionDensity (K:Circle→ℝ) (μ:Measure Circle) (x:Circle) : ℝ :=
  ∫v,K (x-v)∂μ

theorem continuous_convolutionDensity {K:Circle→ℝ} (hK:Continuous K)
    (μ:Measure Circle) [IsFiniteMeasure μ] : Continuous (convolutionDensity K μ) := by
  have hh : Continuous (fun x:Circle=>∫v in (univ:Set Circle),K (x-v)∂μ) :=
    continuous_parametric_integral_of_continuous (μ:=μ) (f:=fun x v:Circle=>K (x-v))
      (hK.comp (continuous_fst.sub continuous_snd)) isCompact_univ
  unfold convolutionDensity
  simpa only [Measure.restrict_univ] using hh

theorem convolutionDensity_nonneg {K:Circle→ℝ} (hK:∀x,0≤K x)
    (μ:Measure Circle) (x:Circle) : 0≤convolutionDensity K μ x :=
  integral_nonneg fun v=>hK (x-v)

theorem translated_kernel_integrable {K:Circle→ℝ} (hK:Continuous K)
    (μ:Measure Circle) [IsFiniteMeasure μ] (x:Circle) : Integrable (fun v=>K (x-v)) μ :=
  (hK.comp (continuous_const.sub continuous_id)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem convolutionDensity_even {K:Circle→ℝ} (hK:Continuous K) (hKeven:∀x,K (-x)=K x)
    {μ:Measure Circle} [IsFiniteMeasure μ] (hμ:Symmetric μ) (x:Circle) :
    convolutionDensity K μ (-x)=convolutionDensity K μ x := by
  unfold convolutionDensity
  have he : ∫v,K (-x-v)∂μ=∫v,K (-x- -v)∂μ := by
    calc
      _ = ∫v,K (-x-v)∂reflect μ := by rw [hμ]
      _ = _ := integral_map measurable_neg.aemeasurable
        (hK.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  rw [he]
  congr 1
  ext v
  rw [show -x- -v= -(x-v) by abel,hKeven]

theorem ofReal_convolutionDensity {K:Circle→ℝ} (hK:Continuous K) (hK0:∀x,0≤K x)
    (μ:Measure Circle) [IsFiniteMeasure μ] (x:Circle) :
    ENNReal.ofReal (convolutionDensity K μ x)=∫⁻v,ENNReal.ofReal (K (x-v))∂μ :=
  ofReal_integral_eq_lintegral_ofReal (translated_kernel_integrable hK μ x)
    (ae_of_all _ fun v=>hK0 (x-v))

end polyak.Global.Circle
