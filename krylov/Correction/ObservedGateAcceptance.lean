import krylov.Correction.ObservedSpectralScaling
import krylov.Correction.GateScaling
import krylov.Stability.UniformGram

/-!
Article: main_krylov, thm:UCq and thm:UCg, genuine quantitative gate acceptance.
Use: Derive both real observed gate decisions from true relative secant errors
and the actual unit-step Gram, with explicit dimension and threshold margins.
Source: original measured pair matrices, genuine diagonal congruence,
Rayleigh form perturbation, Cauchy--Schwarz and the proved spectral norm bounds.
-/

namespace krylov.Correction
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.LinearAlgebra krylov.Stability
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {p : ℕ}

/-- True relative secant errors strictly below one force every actual measured pair energy positive.
Use: Prove actual spectral-gated RFC acceptance in the uniform finite-cycle induction.
Article: main_krylov, thm:UCq and thm:UCg, quantitative observed gate acceptance.
Proof: The genuine unit-step model diagonal lies within the pair-error budget of one; its positive true column scales preserve the sign of the original measured energy.
-/
theorem relative_pair_energy_positive (s y : Fin p → E) (hs : ∀ i, s i≠0)
    {η : ℝ} (hη : η<1) (hy : ∀ i, ‖y i-s i‖≤η*‖s i‖) :
    ∀ i, 0 < inner ℝ (s i) (y i) := by
  intro i
  have ht := (abs_le.mp (unit_pair_energy_bound s y hs hy i)).1
  have hpos : 0 < rescaleModel (pairModel s y) (fun j => ‖s j‖⁻¹) i i := by linarith
  simp only [rescaleModel,Matrix.diagonal_mul,Matrix.mul_diagonal,pairModel,max_self,min_self] at hpos
  by_contra hn
  have henergy : inner ℝ (s i) (y i)≤0 := le_of_not_gt hn
  have hleft := mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr (norm_nonneg (s i))) henergy
  exact (not_lt_of_ge (mul_nonpos_of_nonpos_of_nonneg hleft (inv_nonneg.mpr (norm_nonneg (s i))))) hpos

/-- The actual unit-step latest model differs from the identity by at most its true Gram error plus dimension times relative pair error.
Use: Prove actual spectral-gated RFC acceptance in the uniform finite-cycle induction.
Article: main_krylov, thm:UCq and thm:UCg, quantitative observed gate acceptance.
Proof: Apply the proved genuine model/Gram error estimate and the spectral norm triangle inequality.
-/
theorem normalized_pairModel_identity_distance (s y : Fin p → E) (hs : ∀ i, s i≠0)
    {η δ : ℝ} (hη : 0≤η) (hy : ∀ i, ‖y i-s i‖≤η*‖s i‖)
    (hG : ‖crossGram (unitWindow s) (unitWindow s)-1‖≤δ) :
    ‖rescaleModel (pairModel s y) (fun i => ‖s i‖⁻¹)-1‖≤δ+(p : ℝ)*η := by
  have hmodel := normalized_pairModel_gram_distance s y hs hη hy
  rw [norm_sub_rev] at hmodel
  calc
    _ = ‖(rescaleModel (pairModel s y) (fun i => ‖s i‖⁻¹)-crossGram (unitWindow s) (unitWindow s))+
        (crossGram (unitWindow s) (unitWindow s)-1)‖ := by congr 1; abel
    _ ≤ _ := (norm_add_le _ _).trans ((add_le_add hmodel hG).trans_eq (by ring))

/-- The original measured-energy normalized model has its precise positive lower spectral bound from actual Gram and relative secant errors.
Use: Prove actual spectral-gated RFC acceptance in the uniform finite-cycle induction.
Article: main_krylov, thm:UCq and thm:UCg, quantitative observed gate acceptance.
Proof: The true unit-step model lower endpoint follows by Rayleigh norm perturbation. Its real positive measured-energy scales have squared values at most one plus the pair error. Their genuine inverse diagonal congruence transfers the lower endpoint with the exact reciprocal factor.
-/
theorem observedPairModel_lower_of_gram (s y : Fin p → E) (hs : ∀ i, s i≠0)
    {η δ : ℝ} (hη : 0≤η) (hη1 : η<1) (hy : ∀ i, ‖y i-s i‖≤η*‖s i‖)
    (hG : ‖crossGram (unitWindow s) (unitWindow s)-1‖≤δ)
    (hlower : 0≤1-(δ+(p : ℝ)*η)) :
    ∀ i, (1-(δ+(p : ℝ)*η))/(1+η)≤(observedPairModel_hermitian s y).eigenvalues i := by
  let M := rescaleModel (pairModel s y) (fun i => ‖s i‖⁻¹)
  let q := observedEnergyScale s y
  have he := relative_pair_energy_positive s y hs hη1 hy
  have hq (i : Fin p) : 0<q i := by
    dsimp only [q,observedEnergyScale]
    exact mul_pos (Real.sqrt_pos.mpr (he i)) (inv_pos.mpr (norm_pos_iff.mpr (hs i)))
  have hq2 (i : Fin p) : (q i)^2≤1+η := by
    rw [observedEnergyScale_square s y he]
    have ht := (abs_le.mp (unit_pair_energy_bound s y hs hy i)).2
    linarith
  have hinvq (i : Fin p) : (1+η)⁻¹≤((q i)⁻¹)^2 := by
    rw [inv_pow]
    exact (inv_le_inv₀ (by positivity : 0<1+η) (pow_pos (hq i) 2)).mpr (hq2 i)
  have hmat : diagonal (fun i => (q i)⁻¹)*M*diagonal (fun i => (q i)⁻¹)=observedPairModel s y := by
    have hm := observedPairModel_congruence s y he
    ext i j
    have ht := congrFun (congrFun hm i) j
    simp only [Matrix.diagonal_mul,Matrix.mul_diagonal] at ht ⊢
    change (q i)⁻¹*M i j*(q j)⁻¹=observedPairModel s y i j
    change q i*observedPairModel s y i j*q j=M i j at ht
    rw [← ht]
    field_simp [(hq i).ne',(hq j).ne']
  have hbase : ∀ i, (1 : ℝ)≤(Matrix.isHermitian_one : (1 : Matrix (Fin p) (Fin p) ℝ).IsHermitian).eigenvalues i := by
    apply spectral_lower_of_form
    intro v
    simp only [one_mul,map_one,one_apply_eq_self,real_inner_self_eq_norm_sq,le_refl]
  have hlo := spectral_lower_perturbation 1 M Matrix.isHermitian_one (rescale_pairModel_isHermitian s y _)
    hbase (normalized_pairModel_identity_distance s y hs hη hy hG)
  have hherm : (diagonal (fun i => (q i)⁻¹)*M*diagonal (fun i => (q i)⁻¹)).IsHermitian := by
    rw [hmat]
    exact observedPairModel_hermitian s y
  have h := diagonal_congruence_spectral_lower M (rescale_pairModel_isHermitian s y _)
    (fun i => (q i)⁻¹) hherm hlower hlo hinvq
  simpa only [hmat,div_eq_mul_inv] using h

/-- The original finite measured spectral gate passes under the quantitative true Gram and relative secant-error margin.
Use: Prove actual spectral-gated RFC acceptance in the uniform finite-cycle induction.
Article: main_krylov, thm:UCq and thm:UCg, quantitative observed gate acceptance.
Proof: Derive actual positive measured diagonals and the genuine observed normalized lower spectral endpoint, then use the stated scalar margin for the original gate threshold.
-/
theorem pair_spectralGate_of_gram (s y : Fin p → E) (hs : ∀ i, s i≠0)
    {γ η δ : ℝ} (hγ : 0≤γ) (hη : 0≤η) (hη1 : η<1)
    (hy : ∀ i, ‖y i-s i‖≤η*‖s i‖)
    (hG : ‖crossGram (unitWindow s) (unitWindow s)-1‖≤δ)
    (hmargin : δ+(p : ℝ)*η+γ*η≤1-γ) :
    matrixSpectralGate γ (pairModel s y) := by
  have hlower : 0≤1-(δ+(p : ℝ)*η) := by nlinarith [mul_nonneg hγ hη]
  have hlo := observedPairModel_lower_of_gram s y hs hη hη1 hy hG hlower
  have he := relative_pair_energy_positive s y hs hη1 hy
  refine ⟨?_,?_,?_⟩
  · intro i
    simpa only [pairModel,max_self,min_self] using he i
  · simpa only [diagonalNormalizedModel,observedPairModel,pairModel,max_self,min_self] using observedPairModel_hermitian s y
  · intro i
    have hbound : γ≤(1-(δ+(p : ℝ)*η))/(1+η) := by
      apply (le_div_iff₀ (by positivity : 0<1+η)).mpr
      nlinarith
    simpa only [diagonalNormalizedModel,observedPairModel,pairModel,max_self,min_self] using hbound.trans (hlo i)

/-- Independent positive rescaling of genuine observed columns leaves the actual defect matrix exactly unchanged.
Use: Prove actual spectral-gated RFC acceptance in the uniform finite-cycle induction.
Article: main_krylov, thm:UCq and thm:UCg, quantitative observed gate acceptance.
Proof: Both true cross-pairings acquire the same product of column scales; the original square-root denominator acquires that same positive product and cancels.
-/
theorem pairDefect_rescale_positive (s y : Fin p → E) (d : Fin p → ℝ) (hd : ∀ i, 0<d i) :
    pairDefect (rescaleWindow s d) (rescaleWindow y d)=pairDefect s y := by
  ext i j
  have hc : d i*d j≠0 := (mul_pos (hd i) (hd j)).ne'
  have hden : Real.sqrt ((d i*(d i*inner ℝ (s i) (y i)))*(d j*(d j*inner ℝ (s j) (y j))))=
      (d i*d j)*Real.sqrt (inner ℝ (s i) (y i)*inner ℝ (s j) (y j)) := by
    rw [show (d i*(d i*inner ℝ (s i) (y i)))*(d j*(d j*inner ℝ (s j) (y j)))=
      (d i*d j)^2*(inner ℝ (s i) (y i)*inner ℝ (s j) (y j)) by ring,
      Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq (mul_pos (hd i) (hd j)).le]
  simp only [pairDefect,rescaleWindow,real_inner_smul_left,real_inner_smul_right,hden]
  rw [show d j*(d i*inner ℝ (s i) (y j))-d i*(d j*inner ℝ (s j) (y i))=
      (d i*d j)*(inner ℝ (s i) (y j)-inner ℝ (s j) (y i)) by ring]
  exact mul_div_mul_left _ _ hc

/-- True unit columns with relative image error at most one half have an actual defect spectral norm bounded by four times dimension times error.
Use: Prove actual spectral-gated RFC acceptance in the uniform finite-cycle induction.
Article: main_krylov, thm:UCq and thm:UCg, quantitative observed gate acceptance.
Proof: Cauchy--Schwarz bounds each genuine skew numerator by twice the image error, while the true positive pair energies keep its actual square-root denominator at least one half. The proved spectral/Frobenius comparison sums these entry bounds.
-/
theorem unit_pairDefect_norm_bound (s y : Fin p → E) (hs : ∀ i, ‖s i‖=1)
    {η : ℝ} (hη : 0≤η) (hhalf : η≤1/2) (hy : ∀ i, ‖y i-s i‖≤η) :
    ‖pairDefect s y‖≤(p : ℝ)*(4*η) := by
  have hinner (i j : Fin p) : |inner ℝ (s i) (y j)-inner ℝ (s i) (s j)|≤η := by
    rw [← inner_sub_right]
    have ht := norm_inner_le_norm (𝕜 := ℝ) (s i) (y j-s j)
    rw [Real.norm_eq_abs,hs,one_mul] at ht
    exact ht.trans (hy j)
  have he (i : Fin p) : (1/2 : ℝ)≤ inner ℝ (s i) (y i) := by
    have ht := (abs_le.mp (hinner i i)).1
    rw [real_inner_self_eq_norm_sq,hs,one_pow] at ht
    linarith
  apply (spectral_le_hsNorm _).trans (hsNorm_le_dimension _ (by positivity : 0≤4*η) ?_)
  intro i j
  have hnum : |inner ℝ (s i) (y j)-inner ℝ (s j) (y i)|≤2*η := by
    have hij := hinner i j
    have hji := hinner j i
    rw [real_inner_comm (s i) (s j)] at hji
    have ht := abs_sub (inner ℝ (s i) (y j)-inner ℝ (s i) (s j))
      (inner ℝ (s j) (y i)-inner ℝ (s i) (s j))
    rw [sub_sub_sub_cancel_right] at ht
    linarith
  have hden : (1/2 : ℝ)≤Real.sqrt (inner ℝ (s i) (y i)*inner ℝ (s j) (y j)) := by
    apply Real.le_sqrt_of_sq_le
    have hi := he i
    have hj := he j
    nlinarith [mul_nonneg (sub_nonneg.mpr hi) (sub_nonneg.mpr hj)]
  have hpos : 0 < Real.sqrt (inner ℝ (s i) (y i)*inner ℝ (s j) (y j)) := lt_of_lt_of_le (by norm_num) hden
  change |(inner ℝ (s i) (y j)-inner ℝ (s j) (y i))/
    Real.sqrt (inner ℝ (s i) (y i)*inner ℝ (s j) (y j))|≤4*η
  rw [abs_div,abs_of_pos hpos]
  apply (div_le_iff₀ hpos).mpr
  nlinarith [mul_le_mul_of_nonneg_left hden hη]

/-- Every genuine nonzero observed window has the same length-independent quantitative defect spectral bound from its actual relative secant errors.
Use: Prove actual spectral-gated RFC acceptance in the uniform finite-cycle induction.
Article: main_krylov, thm:UCq and thm:UCg, quantitative observed gate acceptance.
Proof: Normalize the true columns by their own proved positive lengths; exact individual-scale defect invariance and the genuine unit-column estimate preserve the real spectral norm.
-/
theorem relative_pairDefect_norm_bound (s y : Fin p → E) (hs : ∀ i, s i≠0)
    {η : ℝ} (hη : 0≤η) (hhalf : η≤1/2) (hy : ∀ i, ‖y i-s i‖≤η*‖s i‖) :
    ‖pairDefect s y‖≤(p : ℝ)*(4*η) := by
  have hscaled := unit_pairDefect_norm_bound (unitWindow s) (rescaleWindow y (fun i => ‖s i‖⁻¹))
    (unitWindow_norm s hs) hη hhalf (unitWindow_pair_error s y hs hy)
  change ‖pairDefect (rescaleWindow s (fun i => ‖s i‖⁻¹)) (rescaleWindow y (fun i => ‖s i‖⁻¹))‖≤(p : ℝ)*(4*η) at hscaled
  rwa [pairDefect_rescale_positive s y (fun i => ‖s i‖⁻¹)
    (fun i => inv_pos.mpr (norm_pos_iff.mpr (hs i)))] at hscaled

end
end krylov.Correction
