import krylov.Methods.NormalizedCorrection

/-!
Article: main_krylov, lem:projected-residual, the normalized model-error estimate.
Use: obtain the printed pε bound from actual observed pairs, including their
correction-induced secant errors, without dividing by a minimum step length.
Source: the existing spectral/Frobenius comparison and finite Cauchy--Schwarz;
the latest-information convention is the actual newest-first policy convention.
-/

namespace krylov.Methods
noncomputable section
open Matrix krylov.LinearAlgebra
open scoped InnerProductSpace BigOperators Matrix.Norms.L2Operator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {p : ℕ}

/-- Latest-information model for finite arrays in actual newest-first storage order.
Use: expose the actual list-based model to rectangular normalization estimates.
Article: main_krylov, def:latest and lem:projected-residual. -/
def pairModel (s y : Fin p → E) : Matrix (Fin p) (Fin p) ℝ :=
  fun i j => inner ℝ (s (max i j)) (y (min i j))

/-- The finite-array latest model is precisely the model used by the executed policy.
Use: transfer the array estimates to genuine retained and augmented histories.
Article: main_krylov, alg:fc and lem:projected-residual.
Proof: both definitions use the same actual stored steps and observed gradient differences. -/
theorem pairModel_window (W : List (E × E)) :
    pairModel (windowSteps W) (windowImages W)=windowModel W := rfl

/-- Latest-information models transform by the true diagonal coefficient congruence.
Use: the normalized matrix is the rescaled actual model, including incompatible observations.
Article: main_krylov, lem:projected-residual, Ĥ=DHD.
Proof: expand the actual newer-pair inner product and commute its two real scalar factors. -/
theorem pairModel_rescale (s y : Fin p → E) (d : Fin p → ℝ) :
    pairModel (rescaleWindow s d) (rescaleWindow y d)=rescaleModel (pairModel s y) d := by
  ext i j
  simp only [pairModel, rescaleWindow, real_inner_smul_left, real_inner_smul_right,
    rescaleModel, diagonal_mul, mul_diagonal]
  rcases le_total i j with h | h
  · simp only [max_eq_right h, min_eq_left h]; ring
  · simp only [max_eq_left h, min_eq_right h]; ring

/-- The exact Gram pairing is unaffected by selecting the newer index first.
Use: subtract the same reference Gram matrix from true compression and latest model.
Article: main_krylov, lem:projected-residual, normalized reference cancellation.
Proof: real inner-product symmetry handles the sole reversed index order. -/
theorem pairModel_self (s : Fin p → E) : pairModel s s=crossGram s s := by
  ext i j
  rcases le_total i j with h | h
  · simp only [pairModel, max_eq_right h, min_eq_left h, crossGram]
    exact real_inner_comm _ _
  · simp only [pairModel, max_eq_left h, min_eq_right h, crossGram]

/-- True symmetric quadratic observations make the actual latest pair model equal the actual operator compression.
Use: the normalized RFC model error has genuine zero value at its quadratic reference.
Article: main_krylov, lem:projected-residual, reference model cancellation.
Proof: symmetry makes the two possible chronological cross-pairing orders agree. -/
theorem pairModel_quadratic (s : Fin p → E) (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric) :
    pairModel s (fun i => Q (s i))=correctionCompression s Q := by
  ext i j
  rcases le_total i j with h | h
  · change inner ℝ (s (max i j)) (Q (s (min i j)))=inner ℝ (s i) (Q (s j))
    rw [max_eq_right h,min_eq_left h]
    exact (real_inner_comm _ _).trans (hQ (s i) (s j))
  · simp only [pairModel,max_eq_left h,min_eq_right h,correctionCompression,crossGram]

/-- The actual newest-information pair model is a genuine real Hermitian matrix.
Use: its stated spectral interval applies to exactly the matrix used by the policy.
Article: main_krylov, lem:projected-residual.
Proof: interchange the indices; their minimum and maximum are unchanged. -/
theorem pairModel_isHermitian (s y : Fin p → E) : (pairModel s y).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  simp only [pairModel, max_comm j i, min_comm j i, star_trivial]

/-- The actual rectangular column Gram matrix is real Hermitian.
Use: apply the genuine lower and upper spectral bounds to correction synthesis.
Article: main_krylov, lem:projected-residual.
Proof: specialize the proved latest-model symmetry to identical step and image families. -/
theorem crossGram_isHermitian (s : Fin p → E) : (crossGram s s).IsHermitian := by
  rw [← pairModel_self]
  exact pairModel_isHermitian s s

/-- The genuinely rescaled latest-information pair model is real Hermitian.
Use: its eigenvalues are those of the actual normalized coefficient solve.
Article: main_krylov, lem:projected-residual.
Proof: the proved exact diagonal covariance identifies it with a genuine latest pair model. -/
theorem rescale_pairModel_isHermitian (s y : Fin p → E) (d : Fin p → ℝ) :
    (rescaleModel (pairModel s y) d).IsHermitian := by
  rw [← pairModel_rescale]
  exact pairModel_isHermitian _ _

/-- Unit columns and actual normalized pair errors give the dimension-times-error model bound.
Use: ε bounds the true correction operator; η bounds the actual observed pair discrepancies.
Article: main_krylov, lem:projected-residual, ‖N‖≤Cpε.
Proof: each actual entry differs from the same Gram entry by at most ε+η;
the proved Frobenius comparison converts the p² entry energies to p(ε+η). -/
theorem unit_pairModel_error_bound (s y : Fin p → E) (B : E →L[ℝ] E)
    (hs : ∀ i, ‖s i‖=1) {ε η : ℝ} (hε : 0≤ε) (hη : 0≤η)
    (hB : ‖B-ContinuousLinearMap.id ℝ E‖≤ε) (hy : ∀ i, ‖y i-s i‖≤η) :
    ‖correctionCompression s B-pairModel s y‖≤p*(ε+η) := by
  -- The actual observations and actual correction operator are compared to one common Gram matrix.
  have hb (i j : Fin p) : |correctionCompression s B i j-crossGram s s i j|≤ε := by
    change |inner ℝ (s i) (B (s j))-inner ℝ (s i) (s j)|≤ε
    rw [← inner_sub_right]
    have ho := (B-ContinuousLinearMap.id ℝ E).le_opNorm (s j)
    change ‖B (s j)-s j‖≤_ at ho
    rw [hs, mul_one] at ho
    have hi := norm_inner_le_norm (𝕜 := ℝ) (s i) (B (s j)-s j)
    rw [Real.norm_eq_abs, hs, one_mul] at hi
    exact hi.trans (ho.trans hB)
  have hm (i j : Fin p) : |pairModel s y i j-crossGram s s i j|≤η := by
    rw [← pairModel_self s]
    change |inner ℝ (s (max i j)) (y (min i j))-inner ℝ (s (max i j)) (s (min i j))|≤η
    rw [← inner_sub_right]
    have hi := norm_inner_le_norm (𝕜 := ℝ) (s (max i j)) (y (min i j)-s (min i j))
    rw [Real.norm_eq_abs, hs, one_mul] at hi
    exact hi.trans (hy _)
  apply (spectral_le_hsNorm _).trans
  apply hsNorm_le_dimension _ (add_nonneg hε hη)
  intro i j
  change |correctionCompression s B i j-pairModel s y i j|≤ε+η
  calc
    _ = |(correctionCompression s B i j-crossGram s s i j)-
      (pairModel s y i j-crossGram s s i j)| := by congr 1; ring
    _ ≤ |correctionCompression s B i j-crossGram s s i j|+
      |pairModel s y i j-crossGram s s i j| := abs_sub _ _
    _ ≤ ε+η := add_le_add (hb i j) (hm i j)

/-- Actual column-length normalization for an arbitrary rectangular window.
Use: all normalizers are defined from genuine executed physical vectors.
Article: main_krylov, lem:projected-residual, T=[u_i/‖u_i‖]. -/
def unitWindow (s : Fin p → E) : Fin p → E := rescaleWindow s (fun i => ‖s i‖⁻¹)

/-- Every nonzero actual column becomes a genuine unit column.
Use: discharge the unit-vector premise before the normalized pair estimate.
Article: main_krylov, lem:projected-residual.
Proof: positivity of the actual column norm cancels its reciprocal. -/
theorem unitWindow_norm (s : Fin p → E) (hs : ∀ i, s i≠0) (i : Fin p) :
    ‖unitWindow s i‖=1 := by
  rw [unitWindow, rescaleWindow, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr (hs i))]

omit [InnerProductSpace ℝ E] in
/-- The actual column-length diagonal has a nonsingular coefficient determinant.
Use: the physical normalized correction identity has its genuine inverse domain.
Article: main_krylov, lem:projected-residual.
Proof: the diagonal determinant is a finite product of nonzero inverse norms. -/
theorem unitWindow_diagonal_unit (s : Fin p → E) (hs : ∀ i, s i≠0) :
    IsUnit (diagonal (fun i => ‖s i‖⁻¹)).det := by
  rw [det_diagonal, isUnit_iff_ne_zero]
  exact Finset.prod_ne_zero_iff.mpr fun i _ => inv_ne_zero (norm_ne_zero_iff.mpr (hs i))

/-- Relative errors in the actual stored pairs stay uniformly bounded after column normalization.
Use: no lower bound on an individual recorded step length enters the model-error estimate.
Article: main_krylov, lem:projected-residual, normalized y_i−s_i.
Proof: scale the true pair discrepancy by its own positive column norm and cancel that norm. -/
theorem unitWindow_pair_error (s y : Fin p → E) (hs : ∀ i, s i≠0) {η : ℝ}
    (hy : ∀ i, ‖y i-s i‖≤η*‖s i‖) (i : Fin p) :
    ‖rescaleWindow y (fun j => ‖s j‖⁻¹) i-unitWindow s i‖≤η := by
  change ‖‖s i‖⁻¹ • y i-‖s i‖⁻¹ • s i‖≤η
  rw [← smul_sub, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
  exact (mul_le_mul_of_nonneg_left (hy i) (inv_nonneg.mpr (norm_nonneg _))).trans_eq
    (by rw [mul_left_comm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr (hs i)), mul_one])

/-- The actual normalized latest-model error has the printed step-independent pε estimate.
Use: applies directly to every actual retained or augmented RFC pair window.
Article: main_krylov, lem:projected-residual, first bound in eq:projected-residual.
Proof: the actual relative pair error normalizes to η and the actual model
normalizes by diagonal congruence; apply the proved unit-column estimate. -/
theorem normalized_pairModel_error_bound (s y : Fin p → E) (hs : ∀ i, s i≠0)
    (B : E →L[ℝ] E) {ε η : ℝ} (hε : 0≤ε) (hη : 0≤η)
    (hB : ‖B-ContinuousLinearMap.id ℝ E‖≤ε) (hy : ∀ i, ‖y i-s i‖≤η*‖s i‖) :
    ‖correctionCompression (unitWindow s) B-
      rescaleModel (pairModel s y) (fun i => ‖s i‖⁻¹)‖≤p*(ε+η) := by
  rw [← pairModel_rescale]
  exact unit_pairModel_error_bound _ _ B (unitWindow_norm s hs) hε hη hB
    (unitWindow_pair_error s y hs hy)

end
end krylov.Methods
