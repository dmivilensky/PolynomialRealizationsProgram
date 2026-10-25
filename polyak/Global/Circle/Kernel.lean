import polyak.Global.Circle.Moments
import polyak.Global.Kernels.Fourier

/-! The actual periodized source probability kernel and its convolution. -/
noncomputable section
namespace polyak.Global.Circle
open MeasureTheory Set Function
open scoped Topology ENNReal NNReal

def kernel (ε:ℝ) : Measure Circle := (Kernels.kernelMeasure ε).map ofReal

instance kernel_probability (ε:ℝ) : IsProbabilityMeasure (kernel ε) :=
  inferInstanceAs (IsProbabilityMeasure ((Kernels.kernelMeasure ε).map ofReal))

theorem fourier_ofReal (n:ℤ) (x:ℝ) : fourier n (ofReal x)=Complex.exp (((n:ℝ)*x:ℝ)*Complex.I) := by
  change fourier n (x:Circle)=_
  rw [fourier_coe_apply]
  congr 1
  push_cast
  field_simp

theorem integral_kernel_fourier (ε:ℝ) (n:ℤ) :
    ∫x,fourier n x∂kernel ε=(Kernels.kernelHat ε n:ℂ) := by
  rw [kernel,integral_map continuous_ofReal.measurable.aemeasurable
    (fourier n).continuous.aestronglyMeasurable]
  simp_rw [fourier_ofReal]
  convert Kernels.kernel_characteristic ε n using 1
  rw [charFun_apply_real]
  simp only [Complex.ofReal_mul]

theorem kernel_symmetric (ε:ℝ) : Symmetric (kernel ε) := by
  have hr : (Kernels.kernelMeasure ε).map (fun x:ℝ=>-x)=Kernels.kernelMeasure ε := by
    apply Measure.ext_of_charFun
    ext ξ
    have he : (fun x:ℝ=>-x)=(fun x=>(-1:ℝ)*x) := by ext;simp
    rw [he,charFun_map_mul,neg_one_mul,charFun_neg,Kernels.kernel_characteristic]
    simp only [Complex.conj_ofReal]
  unfold Symmetric reflect kernel
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  have he : (fun x:Circle=>-x)∘ofReal=ofReal∘(fun x:ℝ=>-x) := by
    ext x
    exact (map_neg ofReal x).symm
  rw [he,←Measure.map_map (by fun_prop) (by fun_prop),hr]

def smoothMeasure (ε:ℝ) (μ:Measure Circle) : Measure Circle := (kernel ε).conv μ

instance smoothMeasure_probability (ε:ℝ) (μ:Measure Circle) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (smoothMeasure ε μ) :=
  inferInstanceAs (IsProbabilityMeasure ((kernel ε).conv μ))

def negHom : Circle→+Circle where
  toFun x:=-x
  map_zero':=neg_zero
  map_add' x y:=by simp only [neg_add_rev,add_comm]

theorem smoothMeasure_symmetric (ε:ℝ) {μ:Measure Circle} [IsFiniteMeasure μ]
    (hμ:Symmetric μ) : Symmetric (smoothMeasure ε μ) := by
  unfold Symmetric reflect smoothMeasure
  rw [show (fun x:Circle=>-x)=(negHom:Circle→Circle) from rfl,
    Measure.map_conv_addMonoidHom negHom (show Measurable (negHom:Circle→Circle) from continuous_neg.measurable)]
  exact congrArg₂ Measure.conv (kernel_symmetric ε) hμ

end polyak.Global.Circle
