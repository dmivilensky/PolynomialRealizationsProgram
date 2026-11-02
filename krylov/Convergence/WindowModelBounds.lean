import krylov.Convergence.WindowObservations

/-!
Article: main_krylov, thm:Ip and apG:mss.
Use: actual measured secant errors control the actual model, independently of
the sizes of the stored displacements. No model convergence is assumed.
Source: Burdakov83 latest-information selector, exact diagonal rescaling,
and the proved spectral/Frobenius comparison.
-/

namespace krylov.Convergence
noncomputable section
open Matrix krylov.Methods krylov.Secant krylov.Reference krylov.LinearAlgebra
open scoped InnerProductSpace BigOperators Matrix.Norms.L2Operator
variable {n : ℕ}

/-- Actual unit-length normalization of the stored physical steps. -/
def unitWindow {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (s : Fin n → E) : Fin n → E := rescaleWindow s (fun i=>‖s i‖⁻¹)

/-- Apply the same genuine column normalizers to the measured images. -/
def unitWindowImages {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (s y : Fin n → E) : Fin n → E := rescaleWindow y (fun i=>‖s i‖⁻¹)

/-- The actual normalized observed-data error. -/
def windowDataError {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (s y : Fin n → E) : Matrix (Fin n) (Fin n) ℝ :=
  ss1Model s y-crossGram s s

theorem crossGram_windowMatrix (s y : Fin n → EuclideanSpace ℝ (Fin n)) :
    crossGram s y=(windowMatrix s)ᵀ*windowMatrix y := by
  ext i j
  simp only [crossGram,PiLp.inner_apply,RCLike.inner_apply,conj_trivial,
    windowMatrix,Matrix.mul_apply,transpose_apply]
  exact Finset.sum_congr rfl fun a _=>mul_comm _ _

theorem ss1Model_rescale {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (s y : Fin n → E) (d : Fin n → ℝ) :
    ss1Model (rescaleWindow s d) (rescaleWindow y d)=rescaleModel (ss1Model s y) d := by
  have hh : crossGram (rescaleWindow s d) (rescaleWindow y d)=
      diagonal d*crossGram s y*diagonal d := by
    ext i j
    simp only [crossGram,rescaleWindow,real_inner_smul_left,real_inner_smul_right,
      diagonal_mul,mul_diagonal]
    ring
  rw [ss1Model,hh,latest_diagonal_congruence]
  rfl

/-- Changing the actual stored column lengths leaves the physical SS1 query
exactly unchanged. -/
theorem ss1Point_rescale {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (s y : Fin n → E) (d : Fin n → ℝ) (hd : IsUnit (diagonal d).det) (g x : E) :
    ss1Point (rescaleWindow s d) (rescaleWindow y d) g x=ss1Point s y g x := by
  rw [ss1Point,ss1Model_rescale,modelCorrection_rescale _ _ _ hd]
  rfl

theorem unitWindow_norm {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (s : Fin n → E) (hs : ∀ i,s i≠0) (i : Fin n) : ‖unitWindow s i‖=1 := by
  rw [unitWindow,rescaleWindow,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr (hs i))]

theorem unitWindow_diagonal_unit {E : Type*} [NormedAddCommGroup E]
    (s : Fin n → E) (hs : ∀ i,s i≠0) : IsUnit (diagonal (fun i=>‖s i‖⁻¹)).det := by
  rw [det_diagonal,isUnit_iff_ne_zero]
  exact Finset.prod_ne_zero_iff.mpr fun i _=>inv_ne_zero (norm_ne_zero_iff.mpr (hs i))

/-- The normalized error of an actual observed pair is its original relative
error; arbitrarily short nonzero steps cause no loss in the estimate. -/
theorem unitWindow_image_error {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (s y : Fin n → E) (hs : ∀ i,s i≠0) {ε : ℝ}
    (he : ∀ i,‖y i-s i‖≤ε*‖s i‖) (i : Fin n) :
    ‖unitWindowImages s y i-unitWindow s i‖≤ε := by
  change ‖‖s i‖⁻¹ • y i-‖s i‖⁻¹ • s i‖≤ε
  rw [← smul_sub,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
  exact (mul_le_mul_of_nonneg_left (he i) (inv_nonneg.mpr (norm_nonneg _))).trans_eq
    (by field_simp [norm_ne_zero_iff.mpr (hs i)])

/-- The latest selector retains a genuine newer observed secant error in
every entry; symmetry is supplied by the selector itself. -/
theorem windowDataError_entry {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (s y : Fin n → E) (i j : Fin n) :
    windowDataError s y i j=inner ℝ (s (min i j)) (y (max i j)-s (max i j)) := by
  rw [windowDataError,ss1Model,Matrix.sub_apply,latest,crossGram,inner_sub_right]
  congr 1
  rcases le_total i j with h | h
  · simp only [min_eq_left h,max_eq_right h,crossGram]
  · simp only [min_eq_right h,max_eq_left h,crossGram]
    exact real_inner_comm _ _

/-- Genuine unit-column observed errors give the printed n-times normalized
model bound in the spectral matrix norm. -/
theorem windowDataError_norm {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (s y : Fin n → E) (hs : ∀ i,‖s i‖=1) {ε : ℝ} (hε : 0≤ε)
    (he : ∀ i,‖y i-s i‖≤ε) : ‖windowDataError s y‖≤n*ε := by
  apply (spectral_le_hsNorm _).trans
  apply hsNorm_le_dimension _ hε
  intro i j
  rw [windowDataError_entry]
  exact (norm_inner_le_norm (𝕜:=ℝ) _ _).trans (by
    simpa only [hs,one_mul,Real.norm_eq_abs] using he (max i j))

/-- The same p-times budget controls the genuine unsymmetrized observed
cross matrix, including rectangular physical windows. -/
theorem crossGram_error_norm {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (s y : Fin n → E) (hs : ∀ i,‖s i‖=1) {ε : ℝ} (hε : 0≤ε)
    (he : ∀ i,‖y i-s i‖≤ε) : ‖crossGram s y-crossGram s s‖≤n*ε := by
  apply (spectral_le_hsNorm _).trans
  apply hsNorm_le_dimension _ hε
  intro i j
  change |inner ℝ (s i) (y j)-inner ℝ (s i) (s j)|≤ε
  rw [←inner_sub_right]
  exact (norm_inner_le_norm (𝕜:=ℝ) _ _).trans (by
    simpa only [hs,one_mul,Real.norm_eq_abs] using he j)

/-- Removing the actual oldest diagonal leaves only newer observed errors.
This is the data-level reason the sharp oldest-pair estimate has a single
distance denominator rather than a dimension factor. -/
theorem windowDataError_newer_norm {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (s y : Fin (n+1) → E) (hs : ∀ i,‖s i‖=1) {ε : ℝ} (hε : 0≤ε)
    (he : ∀ i, i≠0 → ‖y i-s i‖≤ε) :
    ‖windowDataError s y-windowDataError s y 0 0 •
      vecMulVec (Pi.single 0 1) (Pi.single 0 1)‖≤((n+1:ℕ):ℝ)*ε := by
  apply (spectral_le_hsNorm _).trans
  apply hsNorm_le_dimension _ hε
  intro i j
  by_cases hi : i=0
  · subst i
    by_cases hj : j=0
    · subst j
      simpa only [Matrix.sub_apply,Matrix.smul_apply,Matrix.vecMulVec_apply,
        Pi.single_eq_same,smul_eq_mul,mul_one,sub_self,abs_zero] using hε
    · simp only [Matrix.sub_apply,Matrix.smul_apply,Matrix.vecMulVec_apply,
        Pi.single_eq_same,Pi.single_eq_of_ne hj,mul_zero,smul_eq_mul,sub_zero]
      rw [windowDataError_entry]
      exact (norm_inner_le_norm (𝕜:=ℝ) _ _).trans (by
        simpa only [hs,one_mul,Real.norm_eq_abs,max_eq_right (Fin.zero_le j)] using he j hj)
  · simp only [Matrix.sub_apply,Matrix.smul_apply,Matrix.vecMulVec_apply,
      Pi.single_eq_of_ne hi,zero_mul,smul_eq_mul,mul_zero,sub_zero]
    rw [windowDataError_entry]
    have hm : max i j≠0 := by
      intro hz
      have hh : i≤0 := hz ▸ le_max_left i j
      exact hi (le_antisymm hh (Fin.zero_le i))
    exact (norm_inner_le_norm (𝕜:=ℝ) _ _).trans (by
      simpa only [hs,one_mul,Real.norm_eq_abs] using he (max i j) hm)

/-- The actual square data model has its exact normalized error congruence. -/
theorem window_model_error (s y : Fin n → EuclideanSpace ℝ (Fin n))
    (hs : IsUnit (windowMatrix s).det) :
    inverseCongruence (windowMatrix s) (ss1Model s y)-1=
      inverseCongruence (windowMatrix s) (windowDataError s y) := by
  rw [windowDataError,crossGram_windowMatrix]
  simp only [inverseCongruence,Matrix.mul_sub,Matrix.sub_mul]
  change inverseCongruence (windowMatrix s) (ss1Model s y)-1=
    inverseCongruence (windowMatrix s) (ss1Model s y)-
      inverseCongruence (windowMatrix s) ((windowMatrix s)ᵀ*windowMatrix s)
  rw [inverseCongruence_gram _ hs]

/-- Actual full-window model error under a real normalized-data budget. -/
theorem window_model_norm_bound (s y : Fin n → EuclideanSpace ℝ (Fin n))
    (hunit : IsUnit (windowMatrix s).det) (hs : ∀ i,‖s i‖=1)
    {ε : ℝ} (hε : 0≤ε) (he : ∀ i,‖y i-s i‖≤ε) :
    ‖inverseCongruence (windowMatrix s) (ss1Model s y)-1‖≤
      ‖(windowMatrix s)⁻¹‖^2*(n*ε) := by
  rw [window_model_error _ _ hunit]
  exact (inverseCongruence_norm _ _).trans
    (mul_le_mul_of_nonneg_left (windowDataError_norm s y hs hε he) (sq_nonneg _))

/-- Smallness of the actual model error proves the domain of its inverse,
and bounds that actual inverse by two. -/
theorem secant_inverse_norm_le_two (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : ‖M-1‖≤(1/2:ℝ)) : IsUnit M.det ∧ ‖M⁻¹‖≤2 := by
  have hh : ‖1-M‖<1 := by rw [norm_sub_rev]; linarith
  have hu : IsUnit M := by
    have hi := isUnit_one_sub_of_norm_lt_one hh
    simpa only [sub_sub_cancel] using hi
  have hdet := (Matrix.isUnit_iff_isUnit_det M).mp hu
  refine ⟨hdet,?_⟩
  rw [Matrix.cstar_norm_def]
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro v
  let z : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (M⁻¹*ᵥWithLp.ofLp v)
  have hz : WithLp.toLp 2 (M*ᵥWithLp.ofLp z)=v := by
    change WithLp.toLp 2 (M*ᵥ(M⁻¹*ᵥWithLp.ofLp v))=v
    rw [Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv _ hdet,Matrix.one_mulVec]
  have hd : WithLp.toLp 2 (M*ᵥWithLp.ofLp z)-
      WithLp.toLp 2 ((M-1)*ᵥWithLp.ofLp z)=z := by
    ext i
    simp only [WithLp.ofLp_sub,Pi.sub_apply,Matrix.sub_mulVec,Matrix.one_mulVec]
    ring
  have ht := norm_sub_le (WithLp.toLp 2 (M*ᵥWithLp.ofLp z))
    (WithLp.toLp 2 ((M-1)*ᵥWithLp.ofLp z))
  rw [hd,hz] at ht
  have hb := (Matrix.l2_opNorm_mulVec (M-1) z).trans
    (mul_le_mul_of_nonneg_right hM (norm_nonneg z))
  change ‖WithLp.toLp 2 ((M-1)*ᵥWithLp.ofLp z)‖≤(1/2:ℝ)*‖z‖ at hb
  change ‖z‖≤2*‖v‖
  linarith

end
end krylov.Convergence
