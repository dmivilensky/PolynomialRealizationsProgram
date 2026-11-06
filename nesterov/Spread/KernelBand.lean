import nesterov.Spread.Kernel
import nesterov.Phase.SingleAtom

/-! The actual shifted/scaled convolution probability, in angle and cosine
coordinates, and its exact Fourier integral at every real frequency. -/
namespace nesterov.Spread
noncomputable section
open MeasureTheory Set Complex
open scoped Topology
open polyak.Global.Kernels

def bandMeasure (center width : ℝ) : Measure ℝ :=
  phiMeasure.map (fun x => center+width*x)

instance bandMeasure_probability (center width : ℝ) :
    IsProbabilityMeasure (bandMeasure center width) := by
  unfold bandMeasure
  infer_instance

theorem bandMeasure_characteristic (center width ζ : ℝ) :
    charFun (bandMeasure center width) ζ=
      Complex.exp ((ζ*center:ℝ)*Complex.I)*(canonicalKernel.hat (ζ*width):ℂ) := by
  have he : (fun x : ℝ=>center+width*x)=(fun x=>center+x) ∘ (fun x=>width*x) := rfl
  rw [bandMeasure,he,←Measure.map_map (by fun_prop) (by fun_prop),
    charFun_map_const_add,charFun_map_mul,phi_characteristic,canonicalKernel_hat]
  simp only [RCLike.inner_apply',conj_trivial]
  rw [mul_comm width ζ,mul_comm (phiHat (ζ*width):ℂ)]
  congr 1
  congr 1
  push_cast
  ring

theorem bandMeasure_ae_band (center : ℝ) {width : ℝ} (hw : 0<width) :
    ∀ᵐ ω ∂bandMeasure center width,ω∈Icc (center-width) (center+width) := by
  rw [bandMeasure]
  apply (ae_map_iff (f:=fun x : ℝ=>center+width*x)
    (p:=fun ω=>ω∈Icc (center-width) (center+width)) (by fun_prop) measurableSet_Icc).mpr
  filter_upwards [phiMeasure_ae_support] with x hx
  obtain ⟨hl,hu⟩ := abs_lt.mp hx
  constructor <;> nlinarith

def bandSpectrum (center width : ℝ) : Spectral.Spectrum :=
  ⟨(bandMeasure center width).map Phase.frequency,
    inferInstance⟩

theorem bandSpectrum_ae_angles (center : ℝ) {width : ℝ} (hw : 0<width)
    (hlo : 0≤center-width) (hhi : center+width≤Real.pi) :
    ∀ᵐ q : Spectral.Frequency ∂(bandSpectrum center width : Measure Spectral.Frequency),
      Real.arccos (q:ℝ)∈Icc (center-width) (center+width) := by
  change ∀ᵐ q ∂(bandMeasure center width).map Phase.frequency,_
  rw [ae_map_iff (by unfold Phase.frequency;fun_prop)
    (measurableSet_Icc.preimage (by fun_prop))]
  filter_upwards [bandMeasure_ae_band center hw] with ω hω
  rw [Phase.arccos_frequency ⟨hlo.trans hω.1,hω.2.trans hhi⟩]
  exact hω

theorem bandSpectrum_integral_wave (center : ℝ) {width : ℝ} (hw : 0<width)
    (hlo : 0≤center-width) (hhi : center+width≤Real.pi) (ζ : ℝ) :
    (∫q : Spectral.Frequency,
      Complex.exp ((ζ*Real.arccos (q:ℝ):ℝ)*Complex.I) ∂bandSpectrum center width)=
      Complex.exp ((ζ*center:ℝ)*Complex.I)*(canonicalKernel.hat (ζ*width):ℂ) := by
  change (∫q : Spectral.Frequency,_ ∂(bandMeasure center width).map Phase.frequency)=_
  rw [integral_map (by unfold Phase.frequency;fun_prop) (by fun_prop)]
  rw [←bandMeasure_characteristic center width ζ,charFun_apply_real]
  apply integral_congr_ae
  filter_upwards [bandMeasure_ae_band center hw] with ω hω
  rw [Phase.arccos_frequency ⟨hlo.trans hω.1,hω.2.trans hhi⟩]
  congr 1
  push_cast
  ring

end
end nesterov.Spread
