import krylov.Correction.SpectralGate
import krylov.Methods.HomogeneousCorrection

/-!
Article: main_krylov, def:GRFC, scale invariance of the actual spectral tests.
Use: prove exact covariance of the measured model test under positive
operator scaling and individual positive changes of column coordinates.
Source: real square-root covariance, actual diagonal coefficient congruence
and proof-irrelevant genuine Hermitian eigenvalues. No spectral approximation is used.
-/

namespace krylov.Correction
noncomputable section
open Matrix krylov.Methods
open scoped Matrix.Norms.L2Operator InnerProductSpace
variable {p : ℕ}

/-- Diagonal energy normalization of an actual finite coefficient model.
Use: express the existing observed spectral model without list-dependent index casts.
Article: main_krylov, def:GRFC, Ĥ=diag(H)^(−1/2)Hdiag(H)^(−1/2). -/
def diagonalNormalizedModel (H : Matrix (Fin p) (Fin p) ℝ) : Matrix (Fin p) (Fin p) ℝ :=
  rescaleModel H (fun i => (Real.sqrt (H i i))⁻¹)

/-- Positive individual column rescaling leaves the actual diagonally normalized model exactly unchanged.
Use: physical step and current-direction lengths cannot affect the measured spectral gate.
Article: main_krylov, def:GRFC, invariance under positive coordinate congruence.
Proof: each observed diagonal square root acquires its positive column scale;
the two inverse scales cancel the actual exterior congruence factors entrywise,
including zero or negative observed energies. -/
theorem diagonalNormalizedModel_congruence (H : Matrix (Fin p) (Fin p) ℝ)
    (d : Fin p → ℝ) (hd : ∀ i, 0<d i) :
    diagonalNormalizedModel (rescaleModel H d)=diagonalNormalizedModel H := by
  -- Positivity is required only for the true coordinate scales, not for the observed model diagonal.
  have hs (i : Fin p) : Real.sqrt (rescaleModel H d i i)=d i*Real.sqrt (H i i) := by
    simp only [rescaleModel,diagonal_mul,mul_diagonal]
    rw [show d i*H i i*d i=(d i)^2*H i i by ring,
      Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq (hd i).le]
  ext i j
  have he (M : Matrix (Fin p) (Fin p) ℝ) : diagonalNormalizedModel M i j=
      (Real.sqrt (M i i))⁻¹*M i j*(Real.sqrt (M j j))⁻¹ := by
    simp only [diagonalNormalizedModel,rescaleModel,diagonal_mul,mul_diagonal]
  rw [he,he,hs,hs]
  simp only [rescaleModel,diagonal_mul,mul_diagonal,_root_.mul_inv_rev]
  calc
    _ = ((d i)⁻¹*d i)*((d j)⁻¹*d j)*
        ((Real.sqrt (H i i))⁻¹*H i j*(Real.sqrt (H j j))⁻¹) := by ring
    _ = _ := by rw [inv_mul_cancel₀ (hd i).ne',inv_mul_cancel₀ (hd j).ne',one_mul,one_mul]

/-- A positive common operator factor leaves the real observed normalized model exactly unchanged.
Use: the actual test is insensitive to Hessian units and nonzero common gradient rescaling.
Article: main_krylov, def:GRFC, H↦cH and H↦λ²H.
Proof: positive scalar multiplication is precisely the actual congruence by
its positive square root, whose two exterior factors cancel by the previous theorem. -/
theorem diagonalNormalizedModel_scalar (H : Matrix (Fin p) (Fin p) ℝ)
    {c : ℝ} (hc : 0<c) : diagonalNormalizedModel (c • H)=diagonalNormalizedModel H := by
  have he : c • H=rescaleModel H (fun _ => Real.sqrt c) := by
    ext i j
    simp only [Matrix.smul_apply,smul_eq_mul,rescaleModel,diagonal_mul,mul_diagonal]
    calc
      c*H i j=(Real.sqrt c*Real.sqrt c)*H i j := by rw [Real.mul_self_sqrt hc.le]
      _ = _ := by ring
  rw [he,diagonalNormalizedModel_congruence H _ (fun _ => Real.sqrt_pos.mpr hc)]

/-- The actual spectral test as a predicate of its measured coefficient matrix.
Use: prove matrix covariance once and transfer it to genuine observed windows.
Article: main_krylov, def:GRFC, positive diagonal and λ_min(Ĥ)≥γ_g. -/
def matrixSpectralGate (gamma : ℝ) (H : Matrix (Fin p) (Fin p) ℝ) : Prop :=
  (∀ i, 0<H i i) ∧ ∃ h : (diagonalNormalizedModel H).IsHermitian,
    ∀ i, gamma≤h.eigenvalues i

/-- The finite matrix test is exactly the spectral test of the actual observed policy window.
Use: all matrix covariance results apply to the implemented gate.
Article: main_krylov, def:GRFC, genuine observed test identification.
Proof: the normalized matrices coincide definitionally and Hermitian proofs are irrelevant to their eigenvalues. -/
theorem matrixSpectralGate_window {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (gamma : ℝ) (W : List (E × E)) :
    matrixSpectralGate gamma (windowModel W) ↔ spectralGate gamma W := by
  constructor
  · rintro ⟨hd,h,he⟩
    exact ⟨hd,he⟩
  · intro h
    exact ⟨h.1,observedNormalizedModel_hermitian W,h.2⟩

/-- The complete measured spectral test is invariant under every positive common matrix factor.
Use: preserve both its true diagonal and eigenvalue decisions under operator or initial-gradient scaling.
Article: main_krylov, def:GRFC, common scaling invariance of the spectral tests.
Proof: the actual normalized matrix is identical and positivity of its raw
diagonal is preserved by the strictly positive common factor. -/
theorem matrixSpectralGate_scalar (gamma : ℝ) (H : Matrix (Fin p) (Fin p) ℝ)
    {c : ℝ} (hc : 0<c) : matrixSpectralGate gamma (c • H) ↔ matrixSpectralGate gamma H := by
  simp only [matrixSpectralGate,diagonalNormalizedModel_scalar H hc,Matrix.smul_apply,
    smul_eq_mul,mul_pos_iff_of_pos_left hc]

/-- The complete actual spectral test is invariant under individual positive physical column rescalings.
Use: allow the current direction and old recorded steps to use different positive units.
Article: main_krylov, def:GRFC, invariance of the observed model test.
Proof: actual diagonal congruence leaves the normalized model unchanged;
its two positive diagonal scale factors preserve each true raw energy sign. -/
theorem matrixSpectralGate_congruence (gamma : ℝ) (H : Matrix (Fin p) (Fin p) ℝ)
    (d : Fin p → ℝ) (hd : ∀ i, 0<d i) :
    matrixSpectralGate gamma (rescaleModel H d) ↔ matrixSpectralGate gamma H := by
  unfold matrixSpectralGate
  rw [diagonalNormalizedModel_congruence H d hd]
  simp only [rescaleModel,diagonal_mul,mul_diagonal,mul_pos_iff_of_pos_left (hd _),
    mul_pos_iff_of_pos_right (hd _)]

/-- Nonzero common initial-data scaling preserves the actual finite-pair spectral decision.
Use: the measured spectral half of the GRFC gate agrees at every genuine common gradient scale.
Article: main_krylov, def:GRFC, g₀↦λg₀.
Proof: the true measured pair model scales by λ², which is strictly positive. -/
theorem pairSpectralGate_scalar {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (gamma : ℝ) (s y : Fin p → E) (c : ℝ) (hc : c≠0) :
    matrixSpectralGate gamma (pairModel (fun i => c • s i) (fun i => c • y i)) ↔
      matrixSpectralGate gamma (pairModel s y) := by
  rw [pairModel_scalar]
  exact matrixSpectralGate_scalar gamma _ (mul_self_pos.mpr hc)

end
end krylov.Correction
