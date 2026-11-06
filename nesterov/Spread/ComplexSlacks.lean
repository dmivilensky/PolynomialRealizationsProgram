import nesterov.Spread.Slacks

/-! Literal complex integral forms of the source E± and lag-one identities. -/
namespace nesterov.Spread
noncomputable section
open MeasureTheory Spectral

def wavePlus (a : SymbolPair) (n : ℕ) (c : Frequency) : ℂ :=
  ((g a c:ℂ)+2*Complex.I*skew a c)*
    Complex.exp ((((n:ℝ)*Real.arccos c:ℝ):ℂ)*Complex.I)

private theorem wave_minus_re (g s ω : ℝ) :
    (((g:ℂ)-2*Complex.I*s)*Complex.exp ((ω:ℂ)*Complex.I)).re=
      g*Real.cos ω+2*s*Real.sin ω := by
  simp [Complex.exp_mul_I,Complex.mul_re,Complex.mul_im,Complex.cos_ofReal_re,Complex.sin_ofReal_re]

private theorem wave_plus_re (g s ω : ℝ) :
    (((g:ℂ)+2*Complex.I*s)*Complex.exp ((ω:ℂ)*Complex.I)).re=
      g*Real.cos ω-2*s*Real.sin ω := by
  simp [Complex.exp_mul_I,Complex.mul_re,Complex.mul_im,Complex.cos_ofReal_re,Complex.sin_ofReal_re]

theorem waveMinus_re (a : SymbolPair) (n : ℕ) (c : Frequency) :
    (waveMinus a n c).re=lowerOsc a n c :=
  wave_minus_re _ _ _

theorem wavePlus_re (a : SymbolPair) (n : ℕ) (c : Frequency) :
    (wavePlus a n c).re=upperOsc a n c :=
  wave_plus_re _ _ _

theorem lowerOsc_integral_re (a : SymbolPair) (n : ℕ) (ν : Spectrum) :
    (∫ c,waveMinus a n c ∂ν).re=∫ c,lowerOsc a n c ∂ν := by
  have hi : Integrable (waveMinus a n) (ν:Measure Frequency) :=
    (by unfold waveMinus g skew;fun_prop : Continuous (waveMinus a n)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  calc
    _=∫ c,(waveMinus a n c).re ∂ν := (Complex.reCLM.integral_comp_comm hi).symm
    _=_ := integral_congr_ae (ae_of_all _ (waveMinus_re a n))

theorem upperOsc_integral_re (a : SymbolPair) (n : ℕ) (ν : Spectrum) :
    (∫ c,wavePlus a n c ∂ν).re=∫ c,upperOsc a n c ∂ν := by
  have hi : Integrable (wavePlus a n) (ν:Measure Frequency) :=
    (by unfold wavePlus g skew;fun_prop : Continuous (wavePlus a n)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  calc
    _=∫ c,(wavePlus a n c).re ∂ν := (Complex.reCLM.integral_comp_comm hi).symm
    _=_ := integral_congr_ae (ae_of_all _ (wavePlus_re a n))

theorem lowerSlack_extreme_complex (a : SymbolPair) {t : ℝ} (ht : t<0)
    (ν : Spectrum) (η : ℝ) (n : ℕ) :
    lowerSlack a t ν (-(1-η)*meanG ν a) n=
      meanG ν a*ePlus η (n*|t|)-(∫ c,waveMinus a n c ∂ν).re := by
  rw [lowerOsc_integral_re,lowerSlack_extreme a ht]

theorem upperSlack_extreme_complex (a : SymbolPair) {t : ℝ} (ht : t<0)
    (ν : Spectrum) (η : ℝ) (n : ℕ) :
    upperSlack a t ν (-(1-η)*meanG ν a) n=
      meanG ν a*eMinus η (n*|t|)-(∫ c,wavePlus a n c ∂ν).re := by
  rw [upperOsc_integral_re,upperSlack_extreme a ht]

theorem lagOneSymbol_complex (a : SymbolPair) (t : ℝ) (c : Frequency) :
    ((1-polyak.Waves.z t (Real.arccos c))*((g a c:ℂ)-2*Complex.I*skew a c)).re=
      lagOneSymbol a t c := by
  unfold polyak.Waves.z lagOneSymbol lowerOsc
  rw [Complex.exp_add,Complex.exp_mul_I]
  simp only [←Complex.ofReal_cos,←Complex.ofReal_sin,Complex.exp_ofReal_re,
    Complex.exp_ofReal_im,Complex.mul_re,Complex.mul_im,Complex.sub_re,Complex.sub_im,
    Complex.add_re,Complex.add_im,Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,
    Complex.I_im,Complex.one_re,Complex.one_im]
  norm_num
  ring

end
end nesterov.Spread
