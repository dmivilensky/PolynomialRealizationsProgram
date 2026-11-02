import krylov.Strings.DiscreteEigenEquation
import jacobi.Finite.SpectralUniqueness

/-!
Article: `main_krylov`, `apC:lem:stieltjes(a)`, canonical polynomial dictionary.
Identify the actual mass-gap position polynomials with the canonical
orthonormal polynomials of the genuine full-support boundary spectral
measure. Reuse the proved finite inverse Jacobi theorem and leading-site
spectral identity; no recurrence or spectral identification is hypothesized.
-/

namespace krylov.Strings.DiscreteString
noncomputable section
open Matrix Polynomial chebyshev1 chebyshev2 jacobi.Finite
open scoped BigOperators Matrix.Norms.L2Operator
variable {N : ℕ} (S : DiscreteString N)

/-- Reconstructing the actual full-support string spectral data recovers its
genuine positive-edge Jacobi matrix, including the original ordering. -/
theorem spectralData_reconstructed : S.spectralData.reconstructed = S.jacobi := by
  symm
  apply unique_of_spectral_weights S.jacobi S.spectralData.reconstructed S.jacobi_irreducible
    S.positiveBasis S.spectralData.reconstructedBasis rfl
    (basis_values_injective S.jacobi S.jacobi_irreducible S.positiveBasis)
  intro k
  have hw := S.spectralData.reconstructed_weight (Nat.succ_pos N) k
  have hzero : (⟨0, Nat.succ_pos N⟩ : Fin (N + 1)) = 0 := by apply Fin.ext; simp
  rw [hzero] at hw
  rw [hw]
  change S.positiveBasis.Q 0 k ^ 2 = (S.signMatrix * S.positiveBasis.Q) 0 k ^ 2
  simp only [signMatrix, Matrix.diagonal_mul, Fin.val_zero, pow_zero, one_mul]

/-- Exact values of the normalized leading Jacobi polynomials in their true
eigenbasis, retaining the sign of every spectral component. -/
theorem normalizedLeading_spectral_value (i k : Fin (N + 1)) :
    (normalizedLeading S.jacobi i.val).eval (S.positiveBasis.eigenvalues k) *
      S.positiveBasis.Q 0 k = S.positiveBasis.Q i k := by
  have h := spectral_leading_values S.jacobi S.positiveBasis (Nat.succ_pos N) i.isLt k
  have hzero : (⟨0, Nat.succ_pos N⟩ : Fin (N + 1)) = 0 := by apply Fin.ext; simp
  rw [hzero] at h
  have hi : (⟨i.val, i.isLt⟩ : Fin (N + 1)) = i := rfl
  rw [hi] at h
  have hp := linkProduct_pos S.jacobi_irreducible i.isLt
  simp only [normalizedLeading, eval_mul, eval_C]
  field_simp
  linear_combination h

/-- The physical Stieltjes polynomial has exactly the canonical orthogonal
normalization: its sign alternates while its true mass supplies the norm. -/
theorem orthogonalPolynomial_eq (i : Fin (N + 1)) :
    S.spectralData.orthogonalPolynomial i =
      C ((-1 : ℝ) ^ i.val * Real.sqrt (S.mass i.val)) * S.φPolynomial i.val := by
  have hJ := S.spectralData_reconstructed
  have hnorm : normalizedLeading S.jacobi i.val = S.spectralData.orthogonalPolynomial i := by
    rw [← hJ]
    exact normalizedLeading_eq_orthogonalPolynomial S.spectralData i
  rw [← hnorm]
  apply S.spectralData.evaluate_injective
    ((normalizedLeading_degree_le _ _).trans_lt i.isLt)
    ((natDegree_C_mul_le _ _).trans_lt ((S.polynomialState_degree_le i.val).1.trans_lt i.isLt))
  apply PiLp.ext
  intro k
  have he := S.normalizedLeading_spectral_value i k
  have hp := S.spectralBasis_polynomial i k
  have hq : S.positiveBasis.Q 0 k ≠ 0 := by
    have h := S.spectralBasis_weight_pos k
    change 0 < (S.signMatrix * S.positiveBasis.Q) 0 k ^ 2 at h
    simp only [signMatrix, Matrix.diagonal_mul, Fin.val_zero, pow_zero, one_mul] at h
    exact (sq_pos_iff.mp h)
  change (S.signMatrix * S.positiveBasis.Q) i k =
    Real.sqrt (S.mass i.val) * (S.φPolynomial i.val).eval (S.positiveBasis.eigenvalues k) *
      ((S.signMatrix * S.positiveBasis.Q) 0 k) at hp
  simp only [signMatrix, Matrix.diagonal_mul, Fin.val_zero, pow_zero, one_mul] at hp
  have hv : (normalizedLeading S.jacobi i.val).eval (S.positiveBasis.eigenvalues k) =
      (-1 : ℝ) ^ i.val * Real.sqrt (S.mass i.val) *
        (S.φPolynomial i.val).eval (S.positiveBasis.eigenvalues k) := by
    apply mul_right_cancel₀ hq
    have hs := jacobi.Finite.alternating_sq i.val
    linear_combination he + (-1 : ℝ) ^ i.val * hp - S.positiveBasis.Q i k * hs
  change Real.sqrt (S.spectralData.weight k) *
    (normalizedLeading S.jacobi i.val).eval (S.positiveBasis.eigenvalues k) =
      Real.sqrt (S.spectralData.weight k) *
        (C ((-1 : ℝ) ^ i.val * Real.sqrt (S.mass i.val)) * S.φPolynomial i.val).eval
          (S.positiveBasis.eigenvalues k)
  rw [eval_mul, eval_C, hv]

/-- The literal physical position polynomial has exact degree equal to its
site index, as asserted for every actual finite string. -/
theorem φPolynomial_natDegree (i : Fin (N + 1)) : (S.φPolynomial i.val).natDegree = i.val := by
  have hcoef : (-1 : ℝ) ^ i.val * Real.sqrt (S.mass i.val) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (by norm_num))
      (Real.sqrt_pos.mpr (S.mass_pos i.val (by omega))).ne'
  have h := (S.spectralData.orthogonalPolynomial_degree i).1
  rw [S.orthogonalPolynomial_eq i, natDegree_C_mul hcoef] at h
  exact h

/-- The independently defined normalized Jacobi continuant is exactly
the signed mass-normalized actual physical position polynomial. -/
theorem normalizedLeading_physical (i : Fin (N+1)) :
    normalizedLeading S.jacobi i.val=
      C ((-1 : ℝ)^i.val*Real.sqrt (S.mass i.val))*S.φPolynomial i.val := by
  rw [← S.spectralData_reconstructed, normalizedLeading_eq_orthogonalPolynomial,
    S.orthogonalPolynomial_eq]

end
end krylov.Strings.DiscreteString
