import nesterov.Spread.KernelBand
import nesterov.Spread.FourierMargin
import nesterov.Spread.Slacks
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! The phase defect perturbs each real Fourier moment by at most d/2. -/
namespace nesterov.Spread
noncomputable section
open MeasureTheory Spectral

def cosAverage (ν : Spectrum) (ζ : ℝ) : ℝ :=
  ∫ (c : Frequency),Real.cos (ζ*Real.arccos c) ∂ν

def phaseMean (ν : Spectrum) (Θ : C(Frequency,ℝ)) : ℝ :=
  ∫ (c : Frequency),Real.cos (Θ c) ∂ν

def phaseUpper (ν : Spectrum) (Θ : C(Frequency,ℝ)) (n : ℕ) : ℝ :=
  ∫ (c : Frequency),Real.cos ((n:ℝ)*Real.arccos c+Θ c) ∂ν

def phaseLower (ν : Spectrum) (Θ : C(Frequency,ℝ)) (n : ℕ) : ℝ :=
  ∫ (c : Frequency),Real.cos ((n:ℝ)*Real.arccos c-Θ c) ∂ν

theorem bandSpectrum_cos_average (center : ℝ) {width : ℝ} (hw : 0<width)
    (hlo : 0≤center-width) (hhi : center+width≤Real.pi) (ζ : ℝ) :
    cosAverage (bandSpectrum center width) ζ=
      Real.cos (ζ*center)*canonicalKernel.hat (ζ*width) := by
  have hInt : Integrable (fun c : Frequency=>Complex.exp ((ζ*Real.arccos (c:ℝ):ℝ)*Complex.I))
      (bandSpectrum center width:Measure Frequency) :=
    (by fun_prop : Continuous (fun c : Frequency=>Complex.exp ((ζ*Real.arccos (c:ℝ):ℝ)*Complex.I))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have h := congrArg Complex.re (bandSpectrum_integral_wave center hw hlo hhi ζ)
  have hre : (∫ c : Frequency,Complex.exp ((ζ*Real.arccos (c:ℝ):ℝ)*Complex.I)
      ∂bandSpectrum center width).re=
      ∫ c : Frequency,(Complex.exp ((ζ*Real.arccos (c:ℝ):ℝ)*Complex.I)).re
        ∂bandSpectrum center width := (Complex.reCLM.integral_comp_comm hInt).symm
  rw [hre] at h
  simpa only [cosAverage,Complex.exp_mul_I,Complex.mul_re,Complex.ofReal_re,
    Complex.ofReal_im,zero_mul,sub_zero,Complex.add_re,Complex.cos_ofReal_re,
    Complex.mul_im,Complex.I_re,Complex.I_im,Complex.sin_ofReal_re,Complex.sin_ofReal_im,
    mul_zero,zero_sub,add_zero,mul_one,sub_zero] using h

theorem cosine_integral_perturb (ν : Spectrum) (f h : C(Frequency,ℝ)) {δ : ℝ}
    (hδ : ∀ᵐ (c : Frequency) ∂(ν:Measure Frequency),|f c-h c|≤δ) :
    |(∫ (c : Frequency),Real.cos (f c) ∂ν)-(∫ (c : Frequency),Real.cos (h c) ∂ν)|≤δ := by
  have hf := polyak.Spectral.integrable_continuous ν (by fun_prop : Continuous (fun c=>Real.cos (f c)))
  have hh := polyak.Spectral.integrable_continuous ν (by fun_prop : Continuous (fun c=>Real.cos (h c)))
  have hbound : ∀ᵐ (c : Frequency) ∂(ν:Measure Frequency),‖Real.cos (f c)-Real.cos (h c)‖≤δ := by
    filter_upwards [hδ] with c hc
    exact (Real.abs_cos_sub_cos_le _ _).trans hc
  have h := norm_integral_le_of_norm_le_const hbound
  rw [integral_sub hf hh] at h
  simpa only [Real.norm_eq_abs,Measure.real,measure_univ,ENNReal.toReal_one,mul_one] using h

theorem phaseMean_error (ν : Spectrum) (Θ : C(Frequency,ℝ)) {d : ℝ}
    (hd : ∀ᵐ (c : Frequency) ∂(ν:Measure Frequency),|Real.arccos (c:ℝ)-2*Θ c|≤d) :
    |phaseMean ν Θ-cosAverage ν (1/2)|≤d/2 := by
  let H : C(Frequency,ℝ) := ⟨fun c=>(1/2)*Real.arccos c,by fun_prop⟩
  apply cosine_integral_perturb ν Θ H
  filter_upwards [hd] with c hc
  apply abs_le.mpr
  obtain ⟨hl,hu⟩ := abs_le.mp hc
  dsimp only [H,ContinuousMap.coe_mk]
  constructor <;> linarith

theorem phaseUpper_error (ν : Spectrum) (Θ : C(Frequency,ℝ)) {d : ℝ}
    (hd : ∀ᵐ (c : Frequency) ∂(ν:Measure Frequency),|Real.arccos (c:ℝ)-2*Θ c|≤d) (n : ℕ) :
    |phaseUpper ν Θ n-cosAverage ν ((n:ℝ)+1/2)|≤d/2 := by
  let F : C(Frequency,ℝ) := ⟨fun c=>(n:ℝ)*Real.arccos c+Θ c,by fun_prop⟩
  let H : C(Frequency,ℝ) := ⟨fun c=>((n:ℝ)+1/2)*Real.arccos c,by fun_prop⟩
  apply cosine_integral_perturb ν F H
  filter_upwards [hd] with c hc
  apply abs_le.mpr
  obtain ⟨hl,hu⟩ := abs_le.mp hc
  dsimp only [F,H,ContinuousMap.coe_mk]
  constructor <;> nlinarith

theorem phaseLower_error (ν : Spectrum) (Θ : C(Frequency,ℝ)) {d : ℝ}
    (hd : ∀ᵐ (c : Frequency) ∂(ν:Measure Frequency),|Real.arccos (c:ℝ)-2*Θ c|≤d) (n : ℕ) :
    |phaseLower ν Θ (n+1)-cosAverage ν ((n:ℝ)+1/2)|≤d/2 := by
  let F : C(Frequency,ℝ) := ⟨fun c=>((n+1:ℕ):ℝ)*Real.arccos c-Θ c,by fun_prop⟩
  let H : C(Frequency,ℝ) := ⟨fun c=>((n:ℝ)+1/2)*Real.arccos c,by fun_prop⟩
  apply cosine_integral_perturb ν F H
  filter_upwards [hd] with c hc
  apply abs_le.mpr
  obtain ⟨hl,hu⟩ := abs_le.mp hc
  dsimp only [F,H,ContinuousMap.coe_mk]
  push_cast
  constructor <;> nlinarith

end
end nesterov.Spread
