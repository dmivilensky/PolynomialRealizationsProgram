import nesterov.Spread.Reciprocal
import nesterov.Spread.PhaseAverages

/-! Reciprocal-amplitude weighting converts actual spectral slacks to phase moments. -/
namespace nesterov.Spread
noncomputable section
open MeasureTheory Spectral

theorem polar_coordinates {g s R Θ : ℝ}
    (hpolar : (g:ℂ)-2*Complex.I*s=(R:ℂ)*Complex.exp (-(Θ:ℂ)*Complex.I)) :
    g=R*Real.cos Θ ∧ 2*s=R*Real.sin Θ := by
  have hr := congrArg Complex.re hpolar
  have hi := congrArg Complex.im hpolar
  rw [Complex.exp_mul_I] at hr hi
  constructor
  · simpa [←Complex.ofReal_cos,←Complex.ofReal_sin] using hr
  · simp [←Complex.ofReal_cos,←Complex.ofReal_sin] at hi
    linarith

theorem lowerOsc_polar (a : SymbolPair) (R Θ : C(Frequency,ℝ)) {c : Frequency}
    (hpolar : (g a c:ℂ)-2*Complex.I*skew a c=
      (R c:ℂ)*Complex.exp (-(Θ c:ℂ)*Complex.I)) (n : ℕ) :
    lowerOsc a n c=R c*Real.cos ((n:ℝ)*Real.arccos c-Θ c) := by
  obtain ⟨hg,hs⟩ := polar_coordinates hpolar
  unfold lowerOsc
  rw [hg,hs,Real.cos_sub]
  ring

theorem upperOsc_polar (a : SymbolPair) (R Θ : C(Frequency,ℝ)) {c : Frequency}
    (hpolar : (g a c:ℂ)-2*Complex.I*skew a c=
      (R c:ℂ)*Complex.exp (-(Θ c:ℂ)*Complex.I)) (n : ℕ) :
    upperOsc a n c=R c*Real.cos ((n:ℝ)*Real.arccos c+Θ c) := by
  obtain ⟨hg,hs⟩ := polar_coordinates hpolar
  unfold upperOsc
  rw [hg,hs,Real.cos_add]
  ring

theorem weighted_meanG (a : SymbolPair) (ν : Spectrum) (R Θ : C(Frequency,ℝ))
    (hR : ∀ c,0<R c)
    (hp : ∀ᵐ (c : Frequency) ∂(ν:Measure Frequency),
      (g a c:ℂ)-2*Complex.I*skew a c=(R c:ℂ)*Complex.exp (-(Θ c:ℂ)*Complex.I)) :
    reciprocalZ R ν*meanG (reciprocalProbability R ν hR) a=phaseMean ν Θ := by
  have he : meanG (reciprocalProbability R ν hR) a=
      ∫ c,R c*Real.cos (Θ c) ∂reciprocalProbability R ν hR := by
    apply integral_congr_ae
    filter_upwards [reciprocalProbability_ae R ν hR hp] with c hc
    exact (polar_coordinates hc).1
  rw [he]
  exact reciprocalProbability_cancel_integral R ν hR (fun c=>Real.cos (Θ c))

theorem weighted_lowerOsc (a : SymbolPair) (ν : Spectrum) (R Θ : C(Frequency,ℝ))
    (hR : ∀ c,0<R c)
    (hp : ∀ᵐ (c : Frequency) ∂(ν:Measure Frequency),
      (g a c:ℂ)-2*Complex.I*skew a c=(R c:ℂ)*Complex.exp (-(Θ c:ℂ)*Complex.I)) (n : ℕ) :
    reciprocalZ R ν*(∫ c,lowerOsc a n c ∂reciprocalProbability R ν hR)=phaseLower ν Θ n := by
  have he : (∫ c,lowerOsc a n c ∂reciprocalProbability R ν hR)=
      ∫ c,R c*Real.cos ((n:ℝ)*Real.arccos c-Θ c) ∂reciprocalProbability R ν hR := by
    apply integral_congr_ae
    filter_upwards [reciprocalProbability_ae R ν hR hp] with c hc
    exact lowerOsc_polar a R Θ hc n
  rw [he]
  exact reciprocalProbability_cancel_integral R ν hR (fun c=>Real.cos ((n:ℝ)*Real.arccos c-Θ c))

theorem weighted_upperOsc (a : SymbolPair) (ν : Spectrum) (R Θ : C(Frequency,ℝ))
    (hR : ∀ c,0<R c)
    (hp : ∀ᵐ (c : Frequency) ∂(ν:Measure Frequency),
      (g a c:ℂ)-2*Complex.I*skew a c=(R c:ℂ)*Complex.exp (-(Θ c:ℂ)*Complex.I)) (n : ℕ) :
    reciprocalZ R ν*(∫ c,upperOsc a n c ∂reciprocalProbability R ν hR)=phaseUpper ν Θ n := by
  have he : (∫ c,upperOsc a n c ∂reciprocalProbability R ν hR)=
      ∫ c,R c*Real.cos ((n:ℝ)*Real.arccos c+Θ c) ∂reciprocalProbability R ν hR := by
    apply integral_congr_ae
    filter_upwards [reciprocalProbability_ae R ν hR hp] with c hc
    exact upperOsc_polar a R Θ hc n
  rw [he]
  exact reciprocalProbability_cancel_integral R ν hR (fun c=>Real.cos ((n:ℝ)*Real.arccos c+Θ c))

end
end nesterov.Spread
