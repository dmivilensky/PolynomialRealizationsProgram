import polyak.General.IQC.CertificateIntegral
import polyak.General.IQC.FourierShift
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-! Article: lem:iqc(a). Exact two-channel Fourier/Parseval representation
for every square-summable signal, using the official Haar Fourier unitary. -/
noncomputable section
namespace polyak.General.IQC
open polyak Energy Duality Spectral MeasureTheory
open Fourier
open scoped ENNReal
local instance : Fact (0<2*Real.pi) := ⟨Real.two_pi_pos⟩

variable {m : C(Frequency,ℂ)} {t : ℝ}

def certificateCircleSymbol (cert : StrictCertificate m t) (θ : FrequencyCircle) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  (∑ n ∈ cert.lags,((2*Real.exp (-(n*t)):ℝ):ℂ) •
    ((cert.α n:ℂ) • pairSymbol 1 ((Real.exp (n*t):ℂ)*character (-(n:ℤ)) θ)+
      (cert.β n:ℂ) • pairSymbol (-1) ((Real.exp (n*t):ℂ)*character (-(n:ℤ)) θ)))+
    ((4*cert.γplus:ℝ):ℂ) • starSymbol 1+
    ((4*cert.γminus:ℝ):ℂ) • starSymbol (-1)

theorem certificateCircleSymbol_quadratic (cert : StrictCertificate m t)
    (θ : FrequencyCircle) (x σ : ℂ) :
    matrixQuadratic (certificateCircleSymbol cert θ) ![x,σ]=
      (∑ n ∈ cert.lags,2*Real.exp (-(n*t))*
        (cert.α n*pairQuadratic 1 x (((Real.exp (n*t):ℂ)*character (-(n:ℤ)) θ)*x)
          σ (((Real.exp (n*t):ℂ)*character (-(n:ℤ)) θ)*σ)+
         cert.β n*pairQuadratic (-1) x (((Real.exp (n*t):ℂ)*character (-(n:ℤ)) θ)*x)
          σ (((Real.exp (n*t):ℂ)*character (-(n:ℤ)) θ)*σ)))+
        4*cert.γplus*starQuadratic 1 x σ+4*cert.γminus*starQuadratic (-1) x σ := by
  simp only [certificateCircleSymbol,matrixQuadratic_add,matrixQuadratic_sum,
    matrixQuadratic_real_smul,pairSymbol_quadratic,starSymbol_quadratic]

def frequencyLag (t : ℝ) (n : ℕ) (x : ScalarTime) : ScalarFrequency :=
  scalarUnitary (Real.exp (n*t) • zShift n x)
theorem frequencyLag_ae (t : ℝ) (n : ℕ) (x : ScalarTime) :
    frequencyLag t n x=ᵐ[circleMeasure]
      (fun θ => ((Real.exp (n*t):ℂ)*character (-(n:ℤ)) θ)*scalarUnitary x θ) := by
  rw [frequencyLag,map_smul,scalarUnitary_shift]
  filter_upwards [Lp.coeFn_smul (Real.exp (n*t)) (mulCharacter (-(n:ℤ)) (scalarUnitary x)),
    mulCharacter_ae (-(n:ℤ)) (scalarUnitary x)] with θ hs hm
  rw [hs]
  simp only [Pi.smul_apply,Complex.real_smul]
  rw [hm]
  ring

theorem certificateForm_fourier_integral (cert : StrictCertificate m t) (x σ : ScalarTime) :
    certificateForm cert (x,σ) (x,σ)=
      ∫ θ : FrequencyCircle,matrixQuadratic (certificateCircleSymbol cert θ)
        ![scalarUnitary x θ,scalarUnitary σ θ] ∂circleMeasure := by
  let lag (n : ℕ) (θ : FrequencyCircle) := 2*Real.exp (-(n*t))*
    (cert.α n*pairQuadratic 1 (scalarUnitary x θ) (frequencyLag t n x θ)
      (scalarUnitary σ θ) (frequencyLag t n σ θ)+
     cert.β n*pairQuadratic (-1) (scalarUnitary x θ) (frequencyLag t n x θ)
      (scalarUnitary σ θ) (frequencyLag t n σ θ))
  have hl (n : ℕ) : Integrable (lag n) circleMeasure :=
    (((pairQuadratic_integrable 1 (scalarUnitary x) (frequencyLag t n x)
      (scalarUnitary σ) (frequencyLag t n σ)).const_mul _).add
    ((pairQuadratic_integrable (-1) (scalarUnitary x) (frequencyLag t n x)
      (scalarUnitary σ) (frequencyLag t n σ)).const_mul _)).const_mul _
  have hsum : Integrable (fun θ => ∑ n ∈ cert.lags,lag n θ) circleMeasure :=
    integrable_finsetSum _ (fun n _ => hl n)
  have hp := (starQuadratic_integrable 1 (scalarUnitary x) (scalarUnitary σ)).const_mul (4*cert.γplus)
  have hn := (starQuadratic_integrable (-1) (scalarUnitary x) (scalarUnitary σ)).const_mul (4*cert.γminus)
  have hAEx : ∀ᵐ θ ∂circleMeasure,∀ n,frequencyLag t n x θ=
      ((Real.exp (n*t):ℂ)*character (-(n:ℤ)) θ)*scalarUnitary x θ :=
    ae_all_iff.2 (fun n => frequencyLag_ae t n x)
  have hAEσ : ∀ᵐ θ ∂circleMeasure,∀ n,frequencyLag t n σ θ=
      ((Real.exp (n*t):ℂ)*character (-(n:ℤ)) θ)*scalarUnitary σ θ :=
    ae_all_iff.2 (fun n => frequencyLag_ae t n σ)
  have he : (fun θ => matrixQuadratic (certificateCircleSymbol cert θ)
      ![scalarUnitary x θ,scalarUnitary σ θ])=ᵐ[circleMeasure]
      (fun θ => ((∑ n ∈ cert.lags,lag n θ)+
        4*cert.γplus*starQuadratic 1 (scalarUnitary x θ) (scalarUnitary σ θ))+
        4*cert.γminus*starQuadratic (-1) (scalarUnitary x θ) (scalarUnitary σ θ)) := by
    filter_upwards [hAEx,hAEσ] with θ hx hσ
    rw [certificateCircleSymbol_quadratic]
    dsimp [lag]
    simp only [hx,hσ]
    rfl
  rw [integral_congr_ae he]
  have hlin := integral_add (hsum.add hp) hn
  have hlin' := integral_add hsum hp
  simp only [Pi.add_apply] at hlin hlin'
  rw [hlin,hlin',integral_finsetSum cert.lags (fun n _ => hl n),integral_const_mul,integral_const_mul,
    ← starQuadratic_integral,← starQuadratic_integral,starQuadratic_unitary,starQuadratic_unitary,
    certificateForm_diagonal_formula]
  congr 2
  apply Finset.sum_congr rfl
  intro n _
  dsimp [lag]
  have hl' := integral_add
    ((pairQuadratic_integrable 1 (scalarUnitary x) (frequencyLag t n x)
      (scalarUnitary σ) (frequencyLag t n σ)).const_mul (cert.α n))
    ((pairQuadratic_integrable (-1) (scalarUnitary x) (frequencyLag t n x)
      (scalarUnitary σ) (frequencyLag t n σ)).const_mul (cert.β n))
  rw [integral_const_mul,hl',integral_const_mul,integral_const_mul,← pairQuadratic_integral,← pairQuadratic_integral]
  change _=2*Real.exp (-(n*t))*(cert.α n*pairQuadratic 1 (scalarUnitary x)
    (scalarUnitary (Real.exp (n*t) • zShift n x)) (scalarUnitary σ)
    (scalarUnitary (Real.exp (n*t) • zShift n σ))+
    cert.β n*pairQuadratic (-1) (scalarUnitary x)
    (scalarUnitary (Real.exp (n*t) • zShift n x)) (scalarUnitary σ)
    (scalarUnitary (Real.exp (n*t) • zShift n σ)))
  rw [pairQuadratic_unitary,pairQuadratic_unitary]

/-- Source convention: the Fourier transform uses the negative exponential. -/
def sourceFourier (x : ScalarTime) (θ : FrequencyCircle) : ℂ := scalarUnitary x (-θ)
def sourceCircleSymbol (cert : StrictCertificate m t) (θ : FrequencyCircle) :
    Matrix (Fin 2) (Fin 2) ℂ := certificateCircleSymbol cert (-θ)

theorem sourceCircleSymbol_coe (cert : StrictCertificate m t) (ω : ℝ) :
    sourceCircleSymbol cert (ω : FrequencyCircle)=certificateSymbol cert ω := by
  have hchar (n : ℕ) : character (-(n:ℤ)) (-(ω : FrequencyCircle))=Waves.z 0 ω^n := by
    change (AddCircle.toCircle ((-(n:ℤ)) • (-(ω : FrequencyCircle))) : ℂ)= _
    simp only [smul_neg,neg_smul,neg_neg]
    exact character_nat_eq_wave n ω
  have hwave (n : ℕ) : (Real.exp (n*t):ℂ)*character (-(n:ℤ)) (-(ω : FrequencyCircle))=Waves.z t ω^n := by
    rw [hchar]
    exact exp_mul_unit_wave t ω n
  unfold sourceCircleSymbol certificateCircleSymbol certificateSymbol
  simp only [hwave]

theorem certificateForm_source_fourier_integral (cert : StrictCertificate m t) (x σ : ScalarTime) :
    certificateForm cert (x,σ) (x,σ)=
      ∫ θ : FrequencyCircle,matrixQuadratic (sourceCircleSymbol cert θ)
        ![sourceFourier x θ,sourceFourier σ θ] ∂circleMeasure := by
  rw [certificateForm_fourier_integral]
  exact (integral_neg_eq_self (fun θ : FrequencyCircle =>
    matrixQuadratic (certificateCircleSymbol cert θ) ![scalarUnitary x θ,scalarUnitary σ θ]) circleMeasure).symm

theorem certificateCircle_integrable (cert : StrictCertificate m t) (x σ : ScalarTime) :
    Integrable (fun θ : FrequencyCircle => matrixQuadratic (certificateCircleSymbol cert θ)
      ![scalarUnitary x θ,scalarUnitary σ θ]) circleMeasure := by
  have hpair (n : ℕ) (δ : ℝ) : Integrable (fun θ => pairQuadratic δ (scalarUnitary x θ)
      (((Real.exp (n*t):ℂ)*character (-(n:ℤ)) θ)*scalarUnitary x θ)
      (scalarUnitary σ θ) (((Real.exp (n*t):ℂ)*character (-(n:ℤ)) θ)*scalarUnitary σ θ)) circleMeasure := by
    apply (pairQuadratic_integrable δ (scalarUnitary x) (frequencyLag t n x)
      (scalarUnitary σ) (frequencyLag t n σ)).congr
    filter_upwards [frequencyLag_ae t n x,frequencyLag_ae t n σ] with θ hx hσ
    rw [hx,hσ]
  simp_rw [certificateCircleSymbol_quadratic]
  exact ((integrable_finsetSum cert.lags (fun n _ =>
    (((hpair n 1).const_mul (cert.α n)).add ((hpair n (-1)).const_mul (cert.β n))).const_mul _)).add
    ((starQuadratic_integrable 1 (scalarUnitary x) (scalarUnitary σ)).const_mul _)).add
    ((starQuadratic_integrable (-1) (scalarUnitary x) (scalarUnitary σ)).const_mul _)

theorem sourceCircle_integrable (cert : StrictCertificate m t) (x σ : ScalarTime) :
    Integrable (fun θ : FrequencyCircle => matrixQuadratic (sourceCircleSymbol cert θ)
      ![sourceFourier x θ,sourceFourier σ θ]) circleMeasure :=
  (certificateCircle_integrable cert x σ).comp_neg

end polyak.General.IQC
