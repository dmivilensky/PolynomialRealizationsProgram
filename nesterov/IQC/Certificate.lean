import nesterov.IQC.CertificateTransport
import nesterov.Spectral.Planar
import polyak.General.IQC.HomotopyRealFrequency

/-!
Article: Lemma IQC, both parts. The finite two-channel Hermitian multiplier is
nonnegative on the genuine normalized nonlinear gradient graph, and its value
on arbitrary complex amplitudes is the original division-free spectral symbol.
-/
namespace nesterov.IQC
noncomputable section
open scoped BigOperators
open Spectral
open polyak.General.IQC polyak.Energy polyak.General.IQC.Fourier
variable {a : SymbolPair} {t : ℝ}

@[simp] theorem transported_lags (cert : Duality.StrictCertificate a t) :
    (transported cert).lags=cert.lags := rfl
@[simp] theorem transported_α (cert : Duality.StrictCertificate a t) :
    (transported cert).α=cert.α := rfl
@[simp] theorem transported_β (cert : Duality.StrictCertificate a t) :
    (transported cert).β=cert.β := rfl
@[simp] theorem transported_γplus (cert : Duality.StrictCertificate a t) :
    (transported cert).γplus=cert.γplus := rfl
@[simp] theorem transported_γminus (cert : Duality.StrictCertificate a t) :
    (transported cert).γminus=cert.γminus := rfl

/-- The literal finite Hermitian trigonometric multiplier. -/
def certificateMatrix (cert : Duality.StrictCertificate a t) (ω : ℝ) :
    Matrix (Fin 2) (Fin 2) ℂ:=certificateSymbol (transported cert) ω

/-- On the Fourier circle this is the source convention exp(-ikω). -/
def sourceMatrix (cert : Duality.StrictCertificate a t) (θ : FrequencyCircle) :
    Matrix (Fin 2) (Fin 2) ℂ:=sourceCircleSymbol (transported cert) θ

theorem certificateMatrix_isHermitian (cert : Duality.StrictCertificate a t) (ω : ℝ) :
    (certificateMatrix cert ω).IsHermitian:=certificateSymbol_isHermitian _ _

theorem sourceMatrix_coe (cert : Duality.StrictCertificate a t) (ω : ℝ) :
    sourceMatrix cert (ω:FrequencyCircle)=certificateMatrix cert ω:=sourceCircleSymbol_coe _ _

theorem pairQuadratic_amplitudes (u p : ℂ) (t ω δ : ℝ) (n : ℕ) :
    pairQuadratic δ u (u*polyak.Waves.z t ω^n) p (p*polyak.Waves.z t ω^n)+
      δ*((p*star u).re/2*Real.exp (2*n*t)-(p*star u).re/2)=
      (1/2:ℝ)*Real.exp (n*t)*
        ((Complex.normSq u-Complex.normSq p)*(Real.cosh (n*t)-Real.cos (n*ω))-
          δ*(2*(p*star u).im*Real.sin (n*ω))) := by
  have h:=nesterov.Spectral.Planar.datum_slack u p 0 t ω δ 0 n
  rw [polyak.Energy.pair_slack_eq] at h
  simp only [nesterov.Spectral.Planar.position,nesterov.Spectral.Planar.gradient,
    nesterov.Spectral.Planar.value,polyak.Waves.position,pow_zero,mul_one,
    Nat.cast_zero,mul_zero,zero_add,zero_mul,Complex.normSq_one,
    polyak.Waves.normSq_z_pow] at h
  convert h using 1 <;> ring

theorem starQuadratic_amplitudes (u p : ℂ) (δ : ℝ) :
    starQuadratic δ u p+δ*((p*star u).re/2)=
      (1/4:ℝ)*(Complex.normSq u-Complex.normSq p) := by
  simp only [starQuadratic,Complex.sq_norm,Complex.inner,Complex.mul_re,
    Complex.conj_re,Complex.conj_im,Complex.star_def]
  ring

/-- Evaluation on any pair of complex Fourier amplitudes, independently of
zeros of either amplitude. -/
theorem certificateMatrix_wave (cert : Duality.StrictCertificate a t) (ω : ℝ) (U P : ℂ) :
    matrixQuadratic (certificateMatrix cert ω) ![U,P]=
      certificateQuadratic (transported cert)
        (fun n=>U*polyak.Waves.z 0 ω^n) (fun n=>P*polyak.Waves.z 0 ω^n) 0 := by
  unfold certificateMatrix certificateSymbol
  simp only [matrixQuadratic_add,matrixQuadratic_sum,matrixQuadratic_real_smul,
    pairSymbol_quadratic,starSymbol_quadratic,certificateQuadratic,Nat.zero_add,
    pow_zero,mul_one,Complex.real_smul]
  congr 2
  apply Finset.sum_congr rfl
  intro n _
  have hU : (Real.exp (n*t):ℂ)*(U*polyak.Waves.z 0 ω^n)=polyak.Waves.z t ω^n*U := by
    rw [←mul_assoc,mul_comm _ U,mul_assoc,exp_mul_unit_wave]
    ring
  have hP : (Real.exp (n*t):ℂ)*(P*polyak.Waves.z 0 ω^n)=polyak.Waves.z t ω^n*P := by
    rw [←mul_assoc,mul_comm _ P,mul_assoc,exp_mul_unit_wave]
    ring
  rw [hU,hP]

/-- The frequency symbol is exact even when the query amplitude vanishes. -/
theorem certificateMatrix_graph (cert : Duality.StrictCertificate a t) (c : Frequency) :
    matrixQuadratic (certificateMatrix cert (Real.arccos c)) ![a.u c,a.p c]=
      Duality.symbol a t cert.lags cert.α cert.β cert.γplus cert.γminus c := by
  let U:=a.u c
  let P:=a.p c
  let ω:=Real.arccos c
  let V:=(P*star U).re/2
  have hsplit:=certificateSlack_eq (transported cert)
    (fun n=>U*polyak.Waves.z 0 ω^n) (fun n=>P*polyak.Waves.z 0 ω^n)
    (fun _=>V) 0
  rw [certificateValue_const,add_zero] at hsplit
  have hmatrix:=certificateMatrix_wave cert ω U P
  rw [hmatrix,←hsplit]
  unfold certificateSlack Duality.symbol
  simp only [transported_lags,transported_α,transported_β,transported_γplus,
    transported_γminus,Nat.zero_add,pow_zero,mul_one,Complex.real_smul]
  have hU (n : ℕ) : (Real.exp (n*t):ℂ)*(U*polyak.Waves.z 0 ω^n)=U*polyak.Waves.z t ω^n := by
    rw [←mul_assoc,mul_comm _ U,mul_assoc,exp_mul_unit_wave]
  have hP (n : ℕ) : (Real.exp (n*t):ℂ)*(P*polyak.Waves.z 0 ω^n)=P*polyak.Waves.z t ω^n := by
    rw [←mul_assoc,mul_comm _ P,mul_assoc,exp_mul_unit_wave]
  simp_rw [hU,hP]
  have hp (n : ℕ) : pairQuadratic 1 U (U*polyak.Waves.z t ω^n) P (P*polyak.Waves.z t ω^n)+
      (Real.exp (2*n*t)*V-V)=(1/2:ℝ)*Real.exp (n*t)*(lagA a t n c-lagB a n c) := by
    simpa [V,U,P,ω,lagA,lagB,g,skew,mul_comm] using pairQuadratic_amplitudes U P t ω 1 n
  have hm (n : ℕ) : pairQuadratic (-1) U (U*polyak.Waves.z t ω^n) P (P*polyak.Waves.z t ω^n)-
      (Real.exp (2*n*t)*V-V)=(1/2:ℝ)*Real.exp (n*t)*(lagA a t n c+lagB a n c) := by
    convert pairQuadratic_amplitudes U P t ω (-1) n using 1 <;>
      dsimp [V,U,P,ω,lagA,lagB,g,skew] <;> ring
  simp_rw [hp,hm]
  have he (n : ℕ) : Real.exp (-(n*t))*Real.exp (n*t)=1:=by
    rw [←Real.exp_add]; simp
  have hsum : (∑ n∈cert.lags,2*Real.exp (-(n*t))*
      (cert.α n*((1/2:ℝ)*Real.exp (n*t)*(lagA a t n c-lagB a n c))+
        cert.β n*((1/2:ℝ)*Real.exp (n*t)*(lagA a t n c+lagB a n c))))=
      ∑ n∈cert.lags,(cert.α n*(lagA a t n c-lagB a n c)+
        cert.β n*(lagA a t n c+lagB a n c)) := by
    apply Finset.sum_congr rfl
    intro n _
    calc
      _=(Real.exp (-(n*t))*Real.exp (n*t))*
        (cert.α n*(lagA a t n c-lagB a n c)+cert.β n*(lagA a t n c+lagB a n c)):=by ring
      _=_:=by rw [he,one_mul]
  rw [hsum]
  have hs1:=starQuadratic_amplitudes U P 1
  have hsm:=starQuadratic_amplitudes U P (-1)
  dsimp [V] at *
  simp only [one_mul] at hs1
  simp only [neg_one_mul,←sub_eq_add_neg] at hsm
  rw [hs1,hsm]
  dsimp [U,P,g]
  ring

/-- Lemma IQC(a): the actual discounted normalized gradient satisfies the
whole-line IQC on every real Hilbert space. -/
theorem normalized_gradient_IQC {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E]
    (cert : Duality.StrictCertificate a t) {ψ : E→ℝ} (hψ : polyak.NormalizedSmooth ψ)
    {x : ℤ→E} (hx : ZSquareSummable x) :
    0≤∑' k,zCertificateQuadratic (transported cert) x (zScaledGradient ψ t x) k :=
  normalizedSmooth_IQC (transported cert) hψ hx

/-- Exact source Fourier integral, in every finite real dimension. -/
theorem normalized_gradient_fourier_IQC {I : Type*} [Fintype I]
    (cert : Duality.StrictCertificate a t)
    {ψ : EuclideanSpace ℝ I→ℝ} (hψ : polyak.NormalizedSmooth ψ)
    (x : ZSpace (EuclideanSpace ℝ I)) :
    0≤∫ θ : FrequencyCircle,(∑ i,matrixQuadratic (sourceMatrix cert θ)
      ![sourceFourier (coordinateL2 x i) θ,
        sourceFourier (coordinateL2 (sourceGradientL2 hψ t x) i) θ]) ∂circleMeasure :=
  source_IQC_actual (transported cert) hψ x

/-- The half-line form is positive for the entire homotopy, on genuine
memoryless scaled gradients; square summability follows from nonexpansiveness. -/
theorem halfLine_homotopy_IQC {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E]
    (cert : Duality.StrictCertificate a t) {ψ : E→ℝ} (hψ : polyak.NormalizedSmooth ψ)
    {τ : ℝ} (hτ : τ∈Set.Icc (0:ℝ) 1) (x : SequenceSpace E) :
    0 ≤ iqcValue (halfLineCertificate (transported cert)) x (τ • halfGradientL2 hψ t x) :=
  halfGradientL2_homotopy hψ (transported cert) hτ x

end
end nesterov.IQC
