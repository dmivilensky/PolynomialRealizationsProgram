import polyak.General.IQC.CertificateFourier

/-! Article: lem:iqc(a), blockwise action in every finite spatial dimension.
The dimension-free Hilbert form agrees exactly with the sum of the scalar
Fourier integrals of the actual coordinates. -/
noncomputable section
namespace polyak.General.IQC
open polyak Energy Duality Spectral MeasureTheory
open Fourier
variable {I : Type*} [Fintype I]
variable {m : C(Frequency,ℂ)} {t : ℝ}

def complexCoordinate (x : ℤ → EuclideanSpace ℝ I) (i : I) (k : ℤ) : ℂ := x k i

theorem complexCoordinate_squareSummable (x : ZSpace (EuclideanSpace ℝ I)) (i : I) :
    ZSquareSummable (complexCoordinate x i) := by
  apply Summable.of_nonneg_of_le (fun _ => sq_nonneg _) _ (zlp_squareSummable x)
  intro k
  apply pow_le_pow_left₀ (norm_nonneg _)
  simpa only [complexCoordinate,Complex.norm_real,Real.norm_eq_abs] using PiLp.norm_apply_le (x k) i

def coordinateL2 (x : ZSpace (EuclideanSpace ℝ I)) (i : I) : ScalarTime :=
  toZL2 (complexCoordinate x i) (complexCoordinate_squareSummable x i)
@[simp] theorem coordinateL2_apply (x : ZSpace (EuclideanSpace ℝ I)) (i : I) (k : ℤ) :
    coordinateL2 x i k=(x k i : ℂ) := rfl

theorem pairQuadratic_coordinates (δ : ℝ) (x y σ τ : EuclideanSpace ℝ I) :
    pairQuadratic δ x y σ τ=
      ∑ i,pairQuadratic δ (x i:ℂ) (y i:ℂ) (σ i:ℂ) (τ i:ℂ) := by
  simp only [pairQuadratic,PiLp.norm_sq_eq_of_L2,PiLp.inner_apply]
  simp [Finset.sum_sub_distrib,Finset.mul_sum,Complex.norm_real,Real.norm_eq_abs,sq_abs,
    Complex.inner,← Complex.ofReal_sub]
  simp only [mul_sub,Finset.mul_sum,Finset.sum_sub_distrib]

theorem starQuadratic_coordinates (δ : ℝ) (x σ : EuclideanSpace ℝ I) :
    starQuadratic δ x σ=∑ i,starQuadratic δ (x i:ℂ) (σ i:ℂ) := by
  simp only [starQuadratic,PiLp.norm_sq_eq_of_L2,PiLp.inner_apply]
  simp [Finset.sum_sub_distrib,Finset.mul_sum,Complex.norm_real,Real.norm_eq_abs,sq_abs,Complex.inner]
  simp only [mul_sub,Finset.mul_sum,Finset.sum_sub_distrib]

theorem zCertificateQuadratic_coordinates (cert : StrictCertificate m t)
    (x σ : ℤ → EuclideanSpace ℝ I) (k : ℤ) :
    zCertificateQuadratic cert x σ k=
      ∑ i,zCertificateQuadratic cert (complexCoordinate x i) (complexCoordinate σ i) k := by
  unfold zCertificateQuadratic
  simp only [pairQuadratic_coordinates,starQuadratic_coordinates]
  simp only [Finset.mul_sum,Finset.sum_add_distrib]
  rw [Finset.sum_comm]
  congr 2
  apply Finset.sum_congr rfl
  intro n _
  rw [mul_add,Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp [complexCoordinate,Complex.real_smul,mul_add]

theorem certificateForm_coordinates (cert : StrictCertificate m t)
    (x σ : ZSpace (EuclideanSpace ℝ I)) :
    certificateForm cert (x,σ) (x,σ)=
      ∑ i,certificateForm cert (coordinateL2 x i,coordinateL2 σ i) (coordinateL2 x i,coordinateL2 σ i) := by
  rw [certificateForm_eq_tsum]
  simp_rw [certificateForm_eq_tsum]
  have he (k : ℤ) := zCertificateQuadratic_coordinates cert (fun k=>x k) (fun k=>σ k) k
  conv_lhs => arg 1; ext k; rw [he]
  rw [Summable.tsum_finsetSum]
  · rfl
  · intro i _
    exact summable_zCertificateQuadratic cert (complexCoordinate_squareSummable x i)
      (complexCoordinate_squareSummable σ i)

theorem certificateForm_coordinate_fourier_integral (cert : StrictCertificate m t)
    (x σ : ZSpace (EuclideanSpace ℝ I)) :
    certificateForm cert (x,σ) (x,σ)=
      ∑ i,∫ θ : FrequencyCircle,matrixQuadratic (sourceCircleSymbol cert θ)
        ![sourceFourier (coordinateL2 x i) θ,sourceFourier (coordinateL2 σ i) θ] ∂circleMeasure := by
  rw [certificateForm_coordinates]
  apply Finset.sum_congr rfl
  intro i _
  exact certificateForm_source_fourier_integral cert _ _

theorem source_IQC_coordinate_integrals (cert : StrictCertificate m t)
    {ψ : EuclideanSpace ℝ I → ℝ} (hψ : NormalizedSmooth ψ)
    (x σ : ZSpace (EuclideanSpace ℝ I))
    (hσ : ∀ k,σ k=zScaledGradient ψ t x k) :
    0≤∑ i,∫ θ : FrequencyCircle,matrixQuadratic (sourceCircleSymbol cert θ)
      ![sourceFourier (coordinateL2 x i) θ,sourceFourier (coordinateL2 σ i) θ] ∂circleMeasure := by
  rw [← certificateForm_coordinate_fourier_integral]
  exact certificateForm_nonneg cert hψ x σ hσ

/-- The literal blockwise matrix integral in every finite real dimension. -/
theorem source_IQC_integral (cert : StrictCertificate m t)
    {ψ : EuclideanSpace ℝ I → ℝ} (hψ : NormalizedSmooth ψ)
    (x σ : ZSpace (EuclideanSpace ℝ I))
    (hσ : ∀ k,σ k=zScaledGradient ψ t x k) :
    0≤∫ θ : FrequencyCircle,(∑ i,matrixQuadratic (sourceCircleSymbol cert θ)
      ![sourceFourier (coordinateL2 x i) θ,sourceFourier (coordinateL2 σ i) θ]) ∂circleMeasure := by
  rw [integral_finsetSum Finset.univ (fun i _ => sourceCircle_integrable cert _ _)]
  exact source_IQC_coordinate_integrals cert hψ x σ hσ

theorem source_IQC_actual (cert : StrictCertificate m t)
    {ψ : EuclideanSpace ℝ I → ℝ} (hψ : NormalizedSmooth ψ)
    (x : ZSpace (EuclideanSpace ℝ I)) :
    0≤∫ θ : FrequencyCircle,(∑ i,matrixQuadratic (sourceCircleSymbol cert θ)
      ![sourceFourier (coordinateL2 x i) θ,
        sourceFourier (coordinateL2 (sourceGradientL2 hψ t x) i) θ]) ∂circleMeasure :=
  source_IQC_integral cert hψ x (sourceGradientL2 hψ t x) (fun _ => rfl)

end polyak.General.IQC
