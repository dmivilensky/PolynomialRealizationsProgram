import jacobi.Finite.PolynomialUniqueness
import jacobi.Finite.CholeskyUnique
import jacobi.Finite.SchurGram

/-!
Article: jacobi, Appendix C.4 (gram–Cholesky reconstruction).
The two printed change-of-measure formulas are stated for the actual target
orthonormal polynomials. The factor L may be any positive lower triangular
factor, and each principal inverse and Schur normalization is justified by
independence of the degree-graded weighted evaluations.
Source: finite Gram--Schmidt, Cholesky uniqueness and orthogonal polynomial uniqueness.
Use: the finite change-of-measure identity used in the discrete-to-continuous limit.
-/
namespace jacobi.Finite.DiscreteMeasure
noncomputable section
open Polynomial InnerProductSpace Matrix
open scoped BigOperators InnerProductSpace

variable {N : ℕ} (M : DiscreteMeasure N) (p : Fin N → ℝ[X])

/-- Every positive Cholesky factor gives the same actual target polynomials.
Use: the finite change-of-measure identity used in the discrete-to-continuous limit.
Article: jacobi, Appendix C.4 (gram–Cholesky reconstruction).
Proof: uniqueness identifies the proposed L with the constructed Gram factor,
and polynomial uniqueness identifies its inverse transform with the canonical family. -/
theorem cholesky_formula (hdeg : ∀ i, (p i).natDegree = i.val)
    (hlc : ∀ i, 0 < (p i).leadingCoeff) (L : Matrix (Fin N) (Fin N) ℝ)
    (hL : L.IsLowerTriangular) (hp : ∀ i, 0 < L i i)
    (hG : Matrix.gram ℝ (fun i => M.evaluate (p i)) = L * Lᵀ) (i : Fin N) :
    M.orthogonalPolynomial i = ∑ j, L⁻¹ i j • p j := by
  have he : L = M.gramLower p := Gram.factor_eq (by simp)
    (M.evaluate_linearIndependent p hdeg (fun j => (hlc j).ne')) L hL hp hG
  rw [he, ← M.changeOfMeasure_eq p hdeg hlc i]
  rfl

/-- The row polynomial before its positive Schur normalization.
Use: displays the actual c=-G_<⁻¹G_<,i coefficients in the article's row formula.
Article: jacobi, Appendix C.4 (gram–Cholesky reconstruction).
-/
def schurPolynomial (i : Fin N) : ℝ[X] :=
  p i - ∑ j : Fin i.val,
    Gram.coefficients (fun k : Fin i.val => M.evaluate (p (Gram.before i k)))
      (M.evaluate (p i)) j • p (Gram.before i j)

/-- Weighted evaluation of the row polynomial is the actual orthogonal Schur residual.
Use: transfers the Hilbert-space Schur formula to polynomial equality.
Article: jacobi, Appendix C.4 (gram–Cholesky reconstruction).
Proof: weighted evaluation is linear and commutes with the finite sum. -/
theorem evaluate_schurPolynomial (i : Fin N) :
    M.evaluate (M.schurPolynomial p i) =
      Gram.residual (fun j : Fin i.val => M.evaluate (p (Gram.before i j))) (M.evaluate (p i)) := by
  change M.evaluation (p i-∑ j : Fin i.val, _ • p (Gram.before i j)) = _
  rw [map_sub, map_sum]
  simp only [map_smul, Gram.residual]
  rfl

/-- The row polynomial has no coefficient above its current indexed degree.
Use: bounded-degree evaluation is injective in the final Schur identity.
Article: jacobi, Appendix C.4 (gram–Cholesky reconstruction).
Proof: each correction polynomial has an earlier degree. -/
theorem schurPolynomial_degree_le (hdeg : ∀ i, (p i).natDegree = i.val) (i : Fin N) :
    (M.schurPolynomial p i).natDegree ≤ i.val := by
  -- Every correction term has an earlier degree, so coefficients above the current degree vanish.
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  simp only [schurPolynomial, coeff_sub, finsetSum_coeff, coeff_smul, smul_eq_mul]
  rw [coeff_eq_zero_of_natDegree_lt (by rw [hdeg]; exact hk)]
  have hz : ∑ j : Fin i.val, (Gram.coefficients
      (fun l : Fin i.val => M.evaluate (p (Gram.before i l))) (M.evaluate (p i)) j) *
        (p (Gram.before i j)).coeff k = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    rw [coeff_eq_zero_of_natDegree_lt (by
      rw [hdeg]
      exact j.isLt.trans hk), mul_zero]
  rw [hz, sub_zero]

/-- The printed inverse-principal-block row formula for the canonical target polynomial.
Use: the discrete Gel'fand--Levitan equation in the persymmetric comparison argument.
Article: jacobi, Appendix C.4 (gram–Cholesky reconstruction).
Proof: the normalized Schur residual is normalized Gram--Schmidt; the complete
change-of-measure theorem identifies that basis with the target family, and
bounded-degree evaluation turns the vector identity into polynomial equality. -/
theorem schur_formula (hdeg : ∀ i, (p i).natDegree = i.val)
    (hlc : ∀ i, 0 < (p i).leadingCoeff) (i : Fin N) :
    M.orthogonalPolynomial i =
      (Real.sqrt (Gram.complement (fun j : Fin i.val => M.evaluate (p (Gram.before i j)))
        (M.evaluate (p i))))⁻¹ • M.schurPolynomial p i := by
  -- First identify the vector-level Schur normalization, then use injective bounded-degree polynomial evaluation.
  have hf := M.evaluate_linearIndependent p hdeg (fun j => (hlc j).ne')
  have he := M.evaluate_changeOfMeasure p hdeg hlc i
  rw [M.changeOfMeasure_eq p hdeg hlc i] at he
  have hg : Gram.basis (by simp) (fun j => M.evaluate (p j)) i =
      gramSchmidtNormed ℝ (fun j => M.evaluate (p j)) i :=
    gramSchmidtOrthonormalBasis_apply (by simp) ((gramSchmidtNormed_linearIndependent hf).ne_zero i)
  apply M.evaluate_injective (by rw [(M.orthogonalPolynomial_degree i).1]; exact i.isLt)
    (lt_of_le_of_lt (natDegree_smul_le _ _)
      (lt_of_le_of_lt (M.schurPolynomial_degree_le p hdeg i) i.isLt))
  change M.evaluation (M.orthogonalPolynomial i) = M.evaluation (_ • M.schurPolynomial p i)
  rw [map_smul]
  change M.evaluate (M.orthogonalPolynomial i) = _ • M.evaluate (M.schurPolynomial p i)
  rw [evaluate_schurPolynomial, Gram.normalized_row hf i, he, hg]

end
end jacobi.Finite.DiscreteMeasure
