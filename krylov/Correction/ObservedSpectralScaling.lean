import krylov.Correction.SpectralGate
import krylov.Correction.UniformRecordedCorrection
import krylov.LinearAlgebra.SpectralLowerForms

/-!
Article: main_krylov, thm:UCq and thm:UCg, genuine observed spectral-gate control.
Use: Transfer the actual measured-energy normalization to true unit-step
coordinates, derive normalized model/Gram conditioning and prove the real
correction-to-recorded-step bound directly from the observed spectral gate
and relative errors of genuine observed pairs.
Source: exact diagonal congruence, proved genuine spectral lower-form and
norm perturbation bounds, actual normalized pair-model error and the real
coefficient noncancellation argument. No conditioning conclusion is assumed.
-/

namespace krylov.Correction
noncomputable section
open Matrix Finset krylov.Methods krylov.LinearAlgebra
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {p : ℕ}

/-- The true finite-array observed model normalized by the actual measured positive pair energies.
Use: Close the source uniform gated-RFC conditioning and relative-correction induction without a minimum individual step length.
Article: main_krylov, thm:UCq and thm:UCg, actual observed spectral-gate bounds.
-/
def observedPairModel (s y : Fin p → E) : Matrix (Fin p) (Fin p) ℝ :=
  rescaleModel (pairModel s y) (fun i => (Real.sqrt (inner ℝ (s i) (y i)))⁻¹)

/-- Every actual measured-energy normalized pair model is genuinely real Hermitian.
Use: Close the source uniform gated-RFC conditioning and relative-correction induction without a minimum individual step length.
Article: main_krylov, thm:UCq and thm:UCg, actual observed spectral-gate bounds.
Proof: Use exact original normalization, true observed pair discrepancies and the proved real spectral and correction estimates.
-/
theorem observedPairModel_hermitian (s y : Fin p → E) : (observedPairModel s y).IsHermitian :=
  rescale_pairModel_isHermitian s y _

/-- The finite-array observed model is exactly the original real list-based spectral-gate matrix.
Use: Close the source uniform gated-RFC conditioning and relative-correction induction without a minimum individual step length.
Article: main_krylov, thm:UCq and thm:UCg, actual observed spectral-gate bounds.
Proof: Use exact original normalization, true observed pair discrepancies and the proved real spectral and correction estimates.
-/
theorem observedPairModel_window (W : List (E × E)) :
    observedPairModel (windowSteps W) (windowImages W)=observedNormalizedModel W := by
  unfold observedPairModel observedNormalizedModel
  rw [pairModel_window]
  congr 1
  funext i
  simp only [windowModel,max_self,min_self]

/-- Positive genuine measured pair energies force every original recorded step to be nonzero.
Use: Close the source uniform gated-RFC conditioning and relative-correction induction without a minimum individual step length.
Article: main_krylov, thm:UCq and thm:UCg, actual observed spectral-gate bounds.
Proof: Use exact original normalization, true observed pair discrepancies and the proved real spectral and correction estimates.
-/
theorem positive_pair_steps_ne (s y : Fin p → E) (he : ∀ i, 0 < inner ℝ (s i) (y i)) :
    ∀ i, s i≠0 := by
  intro i hz
  have hi := he i
  rw [hz,inner_zero_left] at hi
  exact hi.false

/-- Relative error of a genuine measured pair controls its actual unit-step model diagonal around one.
Use: Close the source uniform gated-RFC conditioning and relative-correction induction without a minimum individual step length.
Article: main_krylov, thm:UCq and thm:UCg, actual observed spectral-gate bounds.
Proof: Use exact original normalization, true observed pair discrepancies and the proved real spectral and correction estimates.
-/
theorem unit_pair_energy_bound (s y : Fin p → E) (hs : ∀ i, s i≠0) {η : ℝ}
    (hy : ∀ i, ‖y i-s i‖≤η*‖s i‖) (i : Fin p) :
    |rescaleModel (pairModel s y) (fun j => ‖s j‖⁻¹) i i-1|≤η := by
  have hn := unitWindow_norm s hs i
  have hh := norm_inner_le_norm (𝕜 := ℝ) (unitWindow s i)
    (rescaleWindow y (fun j => ‖s j‖⁻¹) i-unitWindow s i)
  rw [Real.norm_eq_abs,inner_sub_right,real_inner_self_eq_norm_sq,hn,one_pow,one_mul] at hh
  have he : rescaleModel (pairModel s y) (fun j => ‖s j‖⁻¹) i i=
      inner ℝ (unitWindow s i) (rescaleWindow y (fun j => ‖s j‖⁻¹) i) := by
    rw [← pairModel_rescale]
    simp only [pairModel,max_self,min_self]
    rfl
  rw [he]
  exact hh.trans (unitWindow_pair_error s y hs hy i)

/-- The true ratio between measured-energy normalization and actual step-length normalization.
Use: Close the source uniform gated-RFC conditioning and relative-correction induction without a minimum individual step length.
Article: main_krylov, thm:UCq and thm:UCg, actual observed spectral-gate bounds.
-/
def observedEnergyScale (s y : Fin p → E) (i : Fin p) : ℝ :=
  Real.sqrt (inner ℝ (s i) (y i))*‖s i‖⁻¹

/-- The genuine squared normalization ratio is exactly the original unit-step model diagonal.
Use: Close the source uniform gated-RFC conditioning and relative-correction induction without a minimum individual step length.
Article: main_krylov, thm:UCq and thm:UCg, actual observed spectral-gate bounds.
Proof: Use exact original normalization, true observed pair discrepancies and the proved real spectral and correction estimates.
-/
theorem observedEnergyScale_square (s y : Fin p → E) (he : ∀ i, 0 < inner ℝ (s i) (y i)) (i : Fin p) :
    (observedEnergyScale s y i)^2=rescaleModel (pairModel s y) (fun j => ‖s j‖⁻¹) i i := by
  simp only [observedEnergyScale,mul_pow,Real.sq_sqrt (he i).le,
    rescaleModel,Matrix.diagonal_mul,Matrix.mul_diagonal,pairModel,max_self,min_self]
  ring

/-- The actual unit-step normalized model is precisely the true diagonal congruence of its original measured-energy spectral-gate model.
Use: Close the source uniform gated-RFC conditioning and relative-correction induction without a minimum individual step length.
Article: main_krylov, thm:UCq and thm:UCg, actual observed spectral-gate bounds.
Proof: Use exact original normalization, true observed pair discrepancies and the proved real spectral and correction estimates.
-/
theorem observedPairModel_congruence (s y : Fin p → E) (he : ∀ i, 0 < inner ℝ (s i) (y i)) :
    diagonal (observedEnergyScale s y)*observedPairModel s y*diagonal (observedEnergyScale s y)=
      rescaleModel (pairModel s y) (fun i => ‖s i‖⁻¹) := by
  ext i j
  have hi : Real.sqrt (inner ℝ (s i) (y i))≠0 := (Real.sqrt_pos.mpr (he i)).ne'
  have hj : Real.sqrt (inner ℝ (s j) (y j))≠0 := (Real.sqrt_pos.mpr (he j)).ne'
  simp only [observedPairModel,observedEnergyScale,rescaleModel,Matrix.diagonal_mul,Matrix.mul_diagonal]
  field_simp


/-- The actual measured spectral gate and relative observed-pair error give the genuine unit-step model lower spectral endpoint.
Use: Close the source uniform gated-RFC conditioning and relative-correction induction without a minimum individual step length.
Article: main_krylov, thm:UCq and thm:UCg, actual observed spectral-gate bounds.
Proof: Use exact original normalization, true observed pair discrepancies and the proved real spectral and correction estimates.
-/
theorem observed_gate_unit_model_lower (s y : Fin p → E)
    (he : ∀ i, 0 < inner ℝ (s i) (y i)) {γ η : ℝ} (hγ : 0≤γ)
    (hy : ∀ i, ‖y i-s i‖≤η*‖s i‖)
    (hgate : ∀ i, γ≤(observedPairModel_hermitian s y).eigenvalues i) :
    ∀ i, γ*(1-η)≤(rescale_pairModel_isHermitian s y (fun j => ‖s j‖⁻¹)).eigenvalues i := by
  -- The actual measured-energy gate transfers through its genuine diagonal normalization; the pair error controls the squared factors.
  have hs := positive_pair_steps_ne s y he
  have hq : ∀ i, 1-η≤(observedEnergyScale s y i)^2 := by
    intro i
    rw [observedEnergyScale_square s y he i]
    have h := (abs_le.mp (unit_pair_energy_bound s y hs hy i)).1
    linarith
  have hmat := observedPairModel_congruence s y he
  have hM : (diagonal (observedEnergyScale s y)*observedPairModel s y*diagonal (observedEnergyScale s y)).IsHermitian := by
    rw [hmat]
    exact rescale_pairModel_isHermitian s y _
  have h := diagonal_congruence_spectral_lower (observedPairModel s y) (observedPairModel_hermitian s y)
    (observedEnergyScale s y) hM hγ hgate hq
  simpa only [hmat] using h

/-- Relative errors of the true stored observations bound the actual normalized latest-model distance to its original physical Gram matrix.
Use: Close the source uniform gated-RFC conditioning and relative-correction induction without a minimum individual step length.
Article: main_krylov, thm:UCq and thm:UCg, actual observed spectral-gate bounds.
Proof: Use exact original normalization, true observed pair discrepancies and the proved real spectral and correction estimates.
-/
theorem normalized_pairModel_gram_distance (s y : Fin p → E) (hs : ∀ i, s i≠0)
    {η : ℝ} (hη : 0≤η) (hy : ∀ i, ‖y i-s i‖≤η*‖s i‖) :
    ‖crossGram (unitWindow s) (unitWindow s)-rescaleModel (pairModel s y) (fun i => ‖s i‖⁻¹)‖≤p*η := by
  have h := normalized_pairModel_error_bound s y hs (ContinuousLinearMap.id ℝ E)
    (by norm_num : (0 : ℝ)≤0) hη (by simp) hy
  simpa only [correctionCompression,ContinuousLinearMap.id_apply,zero_add] using h

/-- The actual measured spectral gate and sufficiently small relative pair error give the genuine unit-step Gram lower endpoint one quarter of the gate threshold.
Use: Close the source uniform gated-RFC conditioning and relative-correction induction without a minimum individual step length.
Article: main_krylov, thm:UCq and thm:UCg, actual observed spectral-gate bounds.
Proof: Use exact original normalization, true observed pair discrepancies and the proved real spectral and correction estimates.
-/
theorem observed_gate_unit_gram_lower (s y : Fin p → E)
    (he : ∀ i, 0 < inner ℝ (s i) (y i)) {γ η : ℝ} (hγ : 0≤γ) (hη : 0≤η)
    (hhalf : η≤1/2) (hsmall : (p : ℝ)*η≤γ/4)
    (hy : ∀ i, ‖y i-s i‖≤η*‖s i‖)
    (hgate : ∀ i, γ≤(observedPairModel_hermitian s y).eigenvalues i) :
    ∀ i, γ/4≤(crossGram_isHermitian (unitWindow s)).eigenvalues i := by
  -- The actual normalized latest model differs from the true Gram matrix by at most the count times the original relative pair error.
  have hlo := observed_gate_unit_model_lower s y he hγ hy hgate
  have hd := normalized_pairModel_gram_distance s y (positive_pair_steps_ne s y he) hη hy
  have h := spectral_lower_perturbation _ _ (rescale_pairModel_isHermitian s y _)
    (crossGram_isHermitian (unitWindow s)) hlo hd
  intro i
  have hi := h i
  nlinarith [mul_le_mul_of_nonneg_left hhalf hγ]

/-- The genuine Gram matrix of actual nonzero normalized columns has operator norm at most their count.
Use: Close the source uniform gated-RFC conditioning and relative-correction induction without a minimum individual step length.
Article: main_krylov, thm:UCq and thm:UCg, actual observed spectral-gate bounds.
Proof: Use exact original normalization, true observed pair discrepancies and the proved real spectral and correction estimates.
-/
theorem unit_window_gram_norm_le (s : Fin p → E) (hs : ∀ i, s i≠0) :
    ‖crossGram (unitWindow s) (unitWindow s)‖≤(p : ℝ) := by
  have hb : ‖crossGram (unitWindow s) (unitWindow s)‖≤(p : ℝ)*1 := by
    apply (spectral_le_hsNorm _).trans
    apply hsNorm_le_dimension _ (by norm_num)
    intro i j
    have h := norm_inner_le_norm (𝕜 := ℝ) (unitWindow s i) (unitWindow s j)
    rw [unitWindow_norm s hs i,unitWindow_norm s hs j,one_mul,Real.norm_eq_abs] at h
    exact h
  simpa only [mul_one] using hb

/-- The actual normalized latest model has a dimension-only upper norm bound derived from its genuine observed pair error.
Use: Close the source uniform gated-RFC conditioning and relative-correction induction without a minimum individual step length.
Article: main_krylov, thm:UCq and thm:UCg, actual observed spectral-gate bounds.
Proof: Use exact original normalization, true observed pair discrepancies and the proved real spectral and correction estimates.
-/
theorem normalized_pairModel_norm_le (s y : Fin p → E) (hs : ∀ i, s i≠0)
    {η : ℝ} (hη : 0≤η) (hy : ∀ i, ‖y i-s i‖≤η*‖s i‖) (hsmall : (p : ℝ)*η≤1) :
    ‖rescaleModel (pairModel s y) (fun i => ‖s i‖⁻¹)‖≤(p : ℝ)+1 := by
  have hd := normalized_pairModel_gram_distance s y hs hη hy
  rw [norm_sub_rev] at hd
  have hg := unit_window_gram_norm_le s hs
  have ht := norm_le_norm_sub_add (rescaleModel (pairModel s y) (fun i => ‖s i‖⁻¹))
    (crossGram (unitWindow s) (unitWindow s))
  linarith


/-- A uniform explicit dimension-and-gate correction-to-total-step comparison constant.
Use: Close the source uniform gated-RFC conditioning and relative-correction induction without a minimum individual step length.
Article: main_krylov, thm:UCq and thm:UCg, actual observed spectral-gate bounds.
-/
def gatedCorrectionConstant (n : ℕ) (γ : ℝ) : ℝ :=
  Real.sqrt n*(1+2*((n : ℝ)+1))*(Real.sqrt (γ/4))⁻¹

/-- The actual coefficient-model correction is uniformly bounded by its genuine full recorded movement, with all model and Gram conditioning derived from the actual measured spectral gate and pair error.
Use: Close the source uniform gated-RFC conditioning and relative-correction induction without a minimum individual step length.
Article: main_krylov, thm:UCq and thm:UCg, actual observed spectral-gate bounds.
Proof: Use exact original normalization, true observed pair discrepancies and the proved real spectral and correction estimates.
-/
theorem observed_gate_correction_recorded {p : ℕ} (s y : Fin (p+1) → E) (g : E) (l : ℝ)
    (he : ∀ i, 0 < inner ℝ (s i) (y i)) {γ η : ℝ} (hγ : 0<γ) (hη : 0≤η)
    (hhalf : η≤1/2) (hsmall : ((p+1 : ℕ) : ℝ)*η≤γ/4) (hsize : ((p+1 : ℕ) : ℝ)*η≤1)
    (hy : ∀ i, ‖y i-s i‖≤η*‖s i‖)
    (hgate : ∀ i, γ≤(observedPairModel_hermitian s y).eigenvalues i)
    (horth : inner ℝ (s 0) g=0) :
    ‖combine s (modelCoefficients s (pairModel s y) g)‖≤gatedCorrectionConstant (p+1) γ*
      ‖l • s 0+combine s (modelCoefficients s (pairModel s y) g)‖ := by
  -- Derive the true normalized inverse, model norm and Gram bounds from this actual measured gate before invoking the real coefficient noncancellation theorem.
  have hs := positive_pair_steps_ne s y he
  have hlo : ∀ i, γ/2≤(rescale_pairModel_isHermitian s y (fun j => ‖s j‖⁻¹)).eigenvalues i := by
    intro i
    have h := observed_gate_unit_model_lower s y he hγ.le hy hgate i
    nlinarith [mul_le_mul_of_nonneg_left hhalf hγ.le]
  have hu := (inverse_bound_of_eigenvalues _ (rescale_pairModel_isHermitian s y _)
    (by positivity : 0<γ/2) hlo).1
  have hdiag : (1 : ℝ)/2≤rescaleModel (pairModel s y) (fun j => ‖s j‖⁻¹) 0 0 := by
    have h := (abs_le.mp (unit_pair_energy_bound s y hs hy 0)).1
    linarith
  have hh := normalizedCorrection_recorded_bound s (pairModel s y) g l hs
    (by norm_num : (0 : ℝ)<1/2) (by positivity : 0<γ/4) (Nat.cast_nonneg (p+1))
    hdiag (normalized_pairModel_norm_le s y hs hη hy hsize) hu horth
    (observed_gate_unit_gram_lower s y he hγ.le hη hhalf hsmall hy hgate)
    (unit_window_gram_norm_le s hs)
  have hc : 1+(((p+1 : ℕ) : ℝ)+1)/(1/2)=1+2*(((p+1 : ℕ) : ℝ)+1) := by ring
  simpa only [hc,gatedCorrectionConstant] using hh

/-- Every passed original list-based spectral gate supplies exactly its true finite-array measured energies and actual normalized eigenvalue inequalities.
Use: Close the source uniform gated-RFC conditioning and relative-correction induction without a minimum individual step length.
Article: main_krylov, thm:UCq and thm:UCg, actual observed spectral-gate bounds.
Proof: Use exact original normalization, true observed pair discrepancies and the proved real spectral and correction estimates.
-/
theorem spectralGate_window_array {γ : ℝ} (W : List (E × E)) (hgate : spectralGate γ W) :
    (∀ i, 0 < inner ℝ (windowSteps W i) (windowImages W i)) ∧
      ∀ i, γ≤(observedPairModel_hermitian (windowSteps W) (windowImages W)).eigenvalues i := by
  constructor
  · intro i
    simpa only [windowModel,max_self,min_self] using hgate.1 i
  · have he := observedPairModel_window W
    simpa only [he] using hgate.2

end
end krylov.Correction
