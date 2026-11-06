import nesterov.Spectral.Compact
import nesterov.Phase.Defect

/-! Exact extreme-charge formulas for the half-step spread construction. -/
namespace nesterov.Spread
noncomputable section
open MeasureTheory Spectral

def ePlus (η x : ℝ) : ℝ := Real.cosh x+(1-η)*Real.sinh x
def eMinus (η x : ℝ) : ℝ := Real.cosh x-(1-η)*Real.sinh x

def lowerSlack (a : SymbolPair) (t : ℝ) (ν : Spectrum) (C : ℝ) (n : ℕ) : ℝ :=
  meanA ν a t n-meanB ν a n+C*Real.sinh (n*t)

def upperSlack (a : SymbolPair) (t : ℝ) (ν : Spectrum) (C : ℝ) (n : ℕ) : ℝ :=
  meanA ν a t n+meanB ν a n-C*Real.sinh (n*t)

def lowerPoint (a : SymbolPair) (t η : ℝ) (n : ℕ) (c : Frequency) : ℝ :=
  lagA a t n c-lagB a n c-(1-η)*g a c*Real.sinh (n*t)

def upperPoint (a : SymbolPair) (t η : ℝ) (n : ℕ) (c : Frequency) : ℝ :=
  lagA a t n c+lagB a n c+(1-η)*g a c*Real.sinh (n*t)

theorem continuous_lowerPoint (a : SymbolPair) (t η : ℝ) (n : ℕ) :
    Continuous (lowerPoint a t η n) := by
  unfold lowerPoint lagA lagB g skew
  fun_prop

theorem continuous_upperPoint (a : SymbolPair) (t η : ℝ) (n : ℕ) :
    Continuous (upperPoint a t η n) := by
  unfold upperPoint lagA lagB g skew
  fun_prop

theorem lowerSlack_eq_integral (a : SymbolPair) (t η : ℝ) (ν : Spectrum) (n : ℕ) :
    lowerSlack a t ν (-(1-η)*meanG ν a) n=∫ c,lowerPoint a t η n c ∂ν := by
  have ha := polyak.Spectral.integrable_continuous ν (continuous_lagA a t n)
  have hb := polyak.Spectral.integrable_continuous ν (continuous_lagB a n)
  have hg := polyak.Spectral.integrable_continuous ν (continuous_g a)
  unfold lowerSlack meanA meanB meanG lowerPoint
  have he := integral_sub (ha.sub hb) ((hg.const_mul (1-η)).mul_const (Real.sinh (n*t)))
  simp only [Pi.sub_apply] at he
  rw [integral_sub ha hb,integral_mul_const,integral_const_mul] at he
  rw [he]
  ring

theorem upperSlack_eq_integral (a : SymbolPair) (t η : ℝ) (ν : Spectrum) (n : ℕ) :
    upperSlack a t ν (-(1-η)*meanG ν a) n=∫ c,upperPoint a t η n c ∂ν := by
  have ha := polyak.Spectral.integrable_continuous ν (continuous_lagA a t n)
  have hb := polyak.Spectral.integrable_continuous ν (continuous_lagB a n)
  have hg := polyak.Spectral.integrable_continuous ν (continuous_g a)
  unfold upperSlack meanA meanB meanG upperPoint
  have he := integral_add (ha.add hb) ((hg.const_mul (1-η)).mul_const (Real.sinh (n*t)))
  simp only [Pi.add_apply] at he
  rw [integral_add ha hb,integral_mul_const,integral_const_mul] at he
  rw [he]
  ring

def waveMinus (a : SymbolPair) (n : ℕ) (c : Frequency) : ℂ :=
  ((g a c:ℂ)-2*Complex.I*skew a c)*
    Complex.exp ((((n:ℝ)*Real.arccos c:ℝ):ℂ)*Complex.I)

def lowerOsc (a : SymbolPair) (n : ℕ) (c : Frequency) : ℝ :=
  g a c*Real.cos (n*Real.arccos c)+2*skew a c*Real.sin (n*Real.arccos c)

def upperOsc (a : SymbolPair) (n : ℕ) (c : Frequency) : ℝ :=
  g a c*Real.cos (n*Real.arccos c)-2*skew a c*Real.sin (n*Real.arccos c)

theorem continuous_lowerOsc (a : SymbolPair) (n : ℕ) : Continuous (lowerOsc a n) := by
  unfold lowerOsc g skew
  fun_prop

theorem continuous_upperOsc (a : SymbolPair) (n : ℕ) : Continuous (upperOsc a n) := by
  unfold upperOsc g skew
  fun_prop

theorem meanA_sub_meanB (a : SymbolPair) (t : ℝ) (ν : Spectrum) (n : ℕ) :
    meanA ν a t n-meanB ν a n=
      meanG ν a*Real.cosh (n*t)-∫ c,lowerOsc a n c ∂ν := by
  have hg := polyak.Spectral.integrable_continuous ν (continuous_g a)
  have hcos : Integrable (fun c : Frequency=>g a c*Real.cos (n*Real.arccos c)) (ν:Measure Frequency) :=
    polyak.Spectral.integrable_continuous ν (by unfold g;fun_prop)
  have hs : Integrable (fun c : Frequency=>2*skew a c*Real.sin (n*Real.arccos c)) (ν:Measure Frequency) :=
    polyak.Spectral.integrable_continuous ν (by unfold skew;fun_prop)
  unfold meanA meanB meanG lagA lowerOsc lagB
  simp_rw [mul_sub]
  rw [integral_sub (hg.mul_const _) hcos,integral_mul_const,integral_add hcos hs]
  ring

theorem meanA_add_meanB (a : SymbolPair) (t : ℝ) (ν : Spectrum) (n : ℕ) :
    meanA ν a t n+meanB ν a n=
      meanG ν a*Real.cosh (n*t)-∫ c,upperOsc a n c ∂ν := by
  have hg := polyak.Spectral.integrable_continuous ν (continuous_g a)
  have hcos : Integrable (fun c : Frequency=>g a c*Real.cos (n*Real.arccos c)) (ν:Measure Frequency) :=
    polyak.Spectral.integrable_continuous ν (by unfold g;fun_prop)
  have hs : Integrable (fun c : Frequency=>2*skew a c*Real.sin (n*Real.arccos c)) (ν:Measure Frequency) :=
    polyak.Spectral.integrable_continuous ν (by unfold skew;fun_prop)
  unfold meanA meanB meanG lagA upperOsc lagB
  simp_rw [mul_sub]
  rw [integral_sub (hg.mul_const _) hcos,integral_mul_const,integral_sub hcos hs]
  ring

theorem lowerSlack_extreme (a : SymbolPair) {t : ℝ} (ht : t<0) (ν : Spectrum)
    (η : ℝ) (n : ℕ) :
    lowerSlack a t ν (-(1-η)*meanG ν a) n=
      meanG ν a*ePlus η (n*|t|)-∫ c,lowerOsc a n c ∂ν := by
  rw [lowerSlack,meanA_sub_meanB,abs_of_neg ht,mul_neg]
  unfold ePlus
  rw [Real.cosh_neg,Real.sinh_neg]
  ring

theorem upperSlack_extreme (a : SymbolPair) {t : ℝ} (ht : t<0) (ν : Spectrum)
    (η : ℝ) (n : ℕ) :
    upperSlack a t ν (-(1-η)*meanG ν a) n=
      meanG ν a*eMinus η (n*|t|)-∫ c,upperOsc a n c ∂ν := by
  rw [upperSlack,meanA_add_meanB,abs_of_neg ht,mul_neg]
  unfold eMinus
  rw [Real.cosh_neg,Real.sinh_neg]
  ring

def lagOneSymbol (a : SymbolPair) (t : ℝ) (c : Frequency) : ℝ :=
  g a c-Real.exp t*lowerOsc a 1 c

theorem lowerSlack_one_extreme (a : SymbolPair) {t : ℝ} (ht : t<0)
    (ν : Spectrum) (η : ℝ) :
    lowerSlack a t ν (-(1-η)*meanG ν a) 1=
      Real.exp (-t)*(∫ c,lagOneSymbol a t c ∂ν)-η*Real.sinh |t| *meanG ν a := by
  have hg := polyak.Spectral.integrable_continuous ν (continuous_g a)
  have ho := polyak.Spectral.integrable_continuous ν (continuous_lowerOsc a 1)
  rw [lowerSlack_extreme a ht ν η]
  unfold lagOneSymbol
  rw [integral_sub hg (ho.const_mul _),integral_const_mul]
  simp only [Nat.cast_one,one_mul]
  have he : ePlus η |t|=Real.exp (-t)-η*Real.sinh |t| := by
    rw [ePlus,abs_of_neg ht]
    have hh := Real.cosh_add_sinh (-t)
    linarith
  rw [he]
  have hex : Real.exp (-t)*Real.exp t=1 := by rw [←Real.exp_add,neg_add_cancel,Real.exp_zero]
  unfold meanG
  linear_combination (∫ c,lowerOsc a 1 c ∂ν)*hex

theorem extreme_charge_reserve {η G : ℝ} (hη : 0<η) (hη1 : η<1) (hG : 0<G) :
    |-(1-η)*G|<G := by
  rw [abs_mul,abs_neg,abs_of_pos (by linarith : 0<1-η),abs_of_pos hG]
  nlinarith

theorem lowerSlack_one_pos_iff (a : SymbolPair) {t : ℝ} (ht : t<0)
    (ν : Spectrum) (η : ℝ) :
    0<lowerSlack a t ν (-(1-η)*meanG ν a) 1 ↔
      η*Real.exp t*Real.sinh |t| *meanG ν a<∫ c,lagOneSymbol a t c ∂ν := by
  have he : Real.exp t*lowerSlack a t ν (-(1-η)*meanG ν a) 1=
      (∫ c,lagOneSymbol a t c ∂ν)-η*Real.exp t*Real.sinh |t| *meanG ν a := by
    rw [lowerSlack_one_extreme a ht]
    rw [mul_sub,←mul_assoc,←Real.exp_add,add_neg_cancel,Real.exp_zero,one_mul]
    ring
  constructor
  · intro h
    have hh := mul_pos (Real.exp_pos t) h
    rw [he] at hh
    linarith
  · intro h
    have hh : 0<Real.exp t*lowerSlack a t ν (-(1-η)*meanG ν a) 1 := by rw [he];linarith
    exact (mul_pos_iff_of_pos_left (Real.exp_pos t)).mp hh

end
end nesterov.Spread
