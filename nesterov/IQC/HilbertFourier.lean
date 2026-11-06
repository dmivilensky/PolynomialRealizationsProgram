import nesterov.IQC.FiniteFourierCompression

/-!
The Fourier IQC on arbitrary real Hilbert carriers. It is constructed as the
continuous extension of genuine finite-coordinate scalar Fourier integrals.
Its equality with the absolutely convergent time form is proved from finite
Parseval identities and density. Thus neither a formal vector Fourier series
nor the identity Q=J is assumed. The extension recovers the literal source
integral in every finite Euclidean space and is independent of compression.
-/
namespace nesterov.IQC
noncomputable section
open scoped BigOperators ENNReal
open Filter MeasureTheory
open polyak.General.IQC polyak.General.IQC.Fourier polyak.Energy
variable {a : Spectral.SymbolPair} {t : ℝ}

section General
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

structure FourierCompression (S : Finset ℤ) (x σ : ZSpace E) where
  dimension : ℕ
  position : ZSpace (EuclideanSpace ℝ (Fin dimension))
  gradient : ZSpace (EuclideanSpace ℝ (Fin dimension))
  embedding : EuclideanSpace ℝ (Fin dimension)→ₗᵢ[ℝ]E
  position_eq : ∀ k,embedding (position k)=zCutoff S x k
  gradient_eq : ∀ k,embedding (gradient k)=zCutoff S σ k

theorem fourierCompression_nonempty (S : Finset ℤ) (x σ : ZSpace E) :
    Nonempty (FourierCompression S x σ) := by
  obtain ⟨d,y,τ,J,hy,hτ⟩:=exists_finite_fourier_compression S x σ
  exact ⟨⟨d,y,τ,J,hy,hτ⟩⟩

def fourierCompression (S : Finset ℤ) (x σ : ZSpace E) : FourierCompression S x σ:=
  Classical.choice (fourierCompression_nonempty S x σ)

/-- An actual finite-coordinate Fourier integral. This definition uses the
scalar source transform and Hermitian multiplier, not the time form. -/
def finiteFourierValue (cert : Duality.StrictCertificate a t) (S : Finset ℤ) (x σ : ZSpace E) : ℝ:=
  let R:=fourierCompression S x σ
  ∑ i : Fin R.dimension,∫ θ : FrequencyCircle,matrixQuadratic (sourceMatrix cert θ)
    ![sourceFourier (coordinateL2 R.position i) θ,
      sourceFourier (coordinateL2 R.gradient i) θ] ∂circleMeasure

/-- Finite Parseval and isometry invariance identify the actual finite
Fourier integral with the Hilbert time form on the truncated signals. -/
theorem finiteFourierValue_eq_time (cert : Duality.StrictCertificate a t)
    (S : Finset ℤ) (x σ : ZSpace E) :
    finiteFourierValue cert S x σ=
      certificateForm (transported cert) (zCutoff S x,zCutoff S σ) (zCutoff S x,zCutoff S σ) := by
  let R:=fourierCompression S x σ
  change (∑ i : Fin R.dimension,∫ θ : FrequencyCircle,matrixQuadratic
    (sourceCircleSymbol (transported cert) θ)
    ![sourceFourier (coordinateL2 R.position i) θ,
      sourceFourier (coordinateL2 R.gradient i) θ] ∂circleMeasure)=_
  rw [←certificateForm_coordinate_fourier_integral]
  exact certificateForm_isometry cert R.embedding R.position R.gradient _ _ R.position_eq R.gradient_eq

/-- Every exact finite spatial compression gives the same actual Fourier
integral. The limit does not depend on a chosen dimension or basis. -/
theorem fourierCompression_integral_eq (cert : Duality.StrictCertificate a t)
    {S : Finset ℤ} {x σ : ZSpace E} (R : FourierCompression S x σ) :
    (∫ θ : FrequencyCircle,(∑ i : Fin R.dimension,matrixQuadratic (sourceMatrix cert θ)
      ![sourceFourier (coordinateL2 R.position i) θ,
        sourceFourier (coordinateL2 R.gradient i) θ]) ∂circleMeasure)=finiteFourierValue cert S x σ := by
  unfold sourceMatrix
  rw [integral_finsetSum Finset.univ (fun i _=>sourceCircle_integrable (transported cert) _ _),
    ←certificateForm_coordinate_fourier_integral,finiteFourierValue_eq_time]
  exact certificateForm_isometry cert R.embedding R.position R.gradient _ _ R.position_eq R.gradient_eq

/-- The finite-coordinate Fourier integrals converge in every real Hilbert
space, with exactly the absolutely convergent whole-line time value. -/
theorem finiteFourierValue_tendsto (cert : Duality.StrictCertificate a t) (x σ : ZSpace E) :
    Tendsto (fun S : Finset ℤ=>finiteFourierValue cert S x σ) atTop
      (nhds (certificateForm (transported cert) (x,σ) (x,σ))) := by
  have hx : Tendsto (fun S : Finset ℤ=>zCutoff S x) atTop (nhds x):=
    lp.hasSum_single (by norm_num : (2:ℝ≥0∞)≠⊤) x
  have hσ : Tendsto (fun S : Finset ℤ=>zCutoff S σ) atTop (nhds σ):=
    lp.hasSum_single (by norm_num : (2:ℝ≥0∞)≠⊤) σ
  have hc : Continuous (fun p : ZSpace E×ZSpace E=>certificateForm (transported cert) p p):=by fun_prop
  simpa only [finiteFourierValue_eq_time,Function.comp_def] using (hc.tendsto (x,σ)).comp (hx.prodMk_nhds hσ)

/-- The canonical Hilbert Fourier IQC is the limit of actual finite
Euclidean Fourier integrals over a common spatial compression of both channels. -/
def hilbertFourierIQC (cert : Duality.StrictCertificate a t) (x σ : ZSpace E) : ℝ:=
  limUnder atTop (fun S : Finset ℤ=>finiteFourierValue cert S x σ)

/-- The all-Hilbert Parseval bridge Q=J, proved by finite-coordinate density. -/
theorem hilbertFourierIQC_eq_time (cert : Duality.StrictCertificate a t) (x σ : ZSpace E) :
    hilbertFourierIQC cert x σ=certificateForm (transported cert) (x,σ) (x,σ) :=
  (finiteFourierValue_tendsto cert x σ).limUnder_eq

theorem hilbertFourierIQC_continuous (cert : Duality.StrictCertificate a t) :
    Continuous (fun p : ZSpace E×ZSpace E=>hilbertFourierIQC cert p.1 p.2) := by
  simp_rw [hilbertFourierIQC_eq_time]
  fun_prop

/-- The source extension is unique: every continuous functional agreeing
with finite-coordinate Fourier integrals agrees on all Hilbert signals. -/
theorem hilbertFourierIQC_unique (cert : Duality.StrictCertificate a t)
    (J : (ZSpace E×ZSpace E)→ℝ) (hJ : Continuous J)
    (hfinite : ∀ (S : Finset ℤ) (x σ : ZSpace E),
      J (zCutoff S x,zCutoff S σ)=finiteFourierValue cert S x σ) (x σ : ZSpace E) :
    J (x,σ)=hilbertFourierIQC cert x σ := by
  have hx : Tendsto (fun S : Finset ℤ=>zCutoff S x) atTop (nhds x):=
    lp.hasSum_single (by norm_num : (2:ℝ≥0∞)≠⊤) x
  have hσ : Tendsto (fun S : Finset ℤ=>zCutoff S σ) atTop (nhds σ):=
    lp.hasSum_single (by norm_num : (2:ℝ≥0∞)≠⊤) σ
  have hj:= (hJ.tendsto (x,σ)).comp (hx.prodMk_nhds hσ)
  simp only [Function.comp_def,hfinite] at hj
  rw [hilbertFourierIQC_eq_time]
  exact tendsto_nhds_unique hj (finiteFourierValue_tendsto cert x σ)

end General

/-- Recovery of the original Fourier integral, on all signals in every
finite Euclidean space, not merely on finite-support signals. -/
theorem hilbertFourierIQC_eq_integral {I : Type*} [Fintype I]
    (cert : Duality.StrictCertificate a t) (x σ : ZSpace (EuclideanSpace ℝ I)) :
    hilbertFourierIQC cert x σ=
      ∫ θ : FrequencyCircle,(∑ i,matrixQuadratic (sourceMatrix cert θ)
        ![sourceFourier (coordinateL2 x i) θ,sourceFourier (coordinateL2 σ i) θ]) ∂circleMeasure := by
  rw [hilbertFourierIQC_eq_time]
  unfold sourceMatrix
  rw [integral_finsetSum Finset.univ (fun i _=>sourceCircle_integrable (transported cert) _ _)]
  exact certificateForm_coordinate_fourier_integral (transported cert) x σ

/-- Lemma IQC(a) on arbitrary real Hilbert spaces, with the canonical
continuous-extension Fourier functional and the genuine nonlinear gradient. -/
theorem normalized_gradient_hilbertFourier_IQC {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E]
    (cert : Duality.StrictCertificate a t) {ψ : E→ℝ} (hψ : polyak.NormalizedSmooth ψ)
    (x : ZSpace E) :
    0 ≤ hilbertFourierIQC cert x (sourceGradientL2 hψ t x) := by
  rw [hilbertFourierIQC_eq_time]
  exact certificateForm_nonneg (transported cert) hψ x _ (fun _=>rfl)

/-- The literal one-sided source data, extended by zero to negative times,
satisfy the all-Hilbert Fourier IQC throughout the whole homotopy. -/
theorem halfline_hilbertFourier_IQC {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E]
    (cert : Duality.StrictCertificate a t) {ψ : E→ℝ} (hψ : polyak.NormalizedSmooth ψ)
    {τ : ℝ} (hτ : τ∈Set.Icc (0:ℝ) 1) (x : SequenceSpace E) :
    0 ≤ hilbertFourierIQC cert (zeroExtendL2 x) (zeroExtendL2 (τ • halfGradientL2 hψ t x)) := by
  rw [hilbertFourierIQC_eq_time]
  exact halfGradientL2_homotopy hψ (transported cert) hτ x

end
end nesterov.IQC
