import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.MeasureTheory.Group.IntegralConvolution
import Mathlib.MeasureTheory.Group.Convolution

/-! The actual even, positive, normalized source bump. -/
noncomputable section
namespace polyak.Global.Kernels
open MeasureTheory Set Function
open scoped NNReal ENNReal
open scoped Topology Convolution ContDiff

def sourceBump : ContDiffBump (0 : ℝ) where
  rIn := 1/8
  rOut := 1/4
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

def psi : ℝ → ℝ := sourceBump.normed volume

theorem psi_nonneg (x : ℝ) : 0≤psi x := sourceBump.nonneg_normed x

theorem psi_even (x : ℝ) : psi (-x)=psi x := sourceBump.normed_neg x

theorem psi_smooth : ContDiff ℝ ∞ psi := sourceBump.contDiff_normed

theorem psi_compact : HasCompactSupport psi := sourceBump.hasCompactSupport_normed

theorem psi_integrable : Integrable psi := sourceBump.integrable_normed

@[simp] theorem integral_psi : ∫x,psi x=1 := sourceBump.integral_normed

theorem psi_support : support psi=Metric.ball (0:ℝ) (1/4) := sourceBump.support_normed_eq

theorem psi_tsupport : tsupport psi=Metric.closedBall (0:ℝ) (1/4) := sourceBump.tsupport_normed_eq

theorem psi_eq_zero_of_abs_ge {x : ℝ} (hx : 1/4≤|x|) : psi x=0 := by
  have hn : x∉support psi := by
    rw [psi_support,Metric.mem_ball,Real.dist_eq,sub_zero,not_lt]
    exact hx
  simpa only [mem_support,not_not] using hn

def psiMeasure : Measure ℝ := volume.withDensity (fun x=>ENNReal.ofReal (psi x))

instance psiMeasure_probability : IsProbabilityMeasure psiMeasure := by
  constructor
  rw [psiMeasure,withDensity_apply _ MeasurableSet.univ]
  simp only [Measure.restrict_univ]
  rw [←ofReal_integral_eq_lintegral_ofReal psi_integrable (ae_of_all _ psi_nonneg),integral_psi]
  norm_num

@[simp] theorem integral_psiMeasure {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ→E) : ∫x,f x ∂psiMeasure=∫x,psi x • f x := by
  let w : ℝ→ℝ≥0 := fun x=>⟨psi x,psi_nonneg x⟩
  have hw : Measurable w := psi_smooth.continuous.measurable.subtype_mk
  have he : (fun x=>ENNReal.ofReal (psi x))=(fun x=>(w x:ℝ≥0∞)) := by
    funext x
    exact ENNReal.ofReal_eq_coe_nnreal (psi_nonneg x)
  rw [psiMeasure,he,integral_withDensity_eq_integral_smul hw]
  rfl

end polyak.Global.Kernels
