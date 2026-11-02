import jacobi.Finite.ChangeOfMeasure

/-!
Article: jacobi, Appendix C.4 (gram–Cholesky reconstruction).
The orthonormal polynomials of any positive discrete spectral measure are
constructed from monomials by the proved Appendix C.4 transformation.
This supplies the polynomial basis for the Lanczos--Stieltjes reconstruction.
Source: de Boor and Golub, The numerically stable reconstruction of a Jacobi matrix
from spectral data; Gram--Schmidt on a finite spectral measure.
Use: defines the finite spectral reconstruction without postulating orthogonal polynomials.
-/

namespace jacobi.Finite.DiscreteMeasure
noncomputable section
open Polynomial InnerProductSpace
open scoped BigOperators InnerProductSpace

variable {N : ℕ} (M : DiscreteMeasure N)

/-- The canonical orthonormal polynomial of each degree below the support size.
Use: defines the finite spectral reconstruction without postulating orthogonal polynomials.
Article: jacobi, Equation (1.3) (unique persymmetric realization and its weights).
-/
def orthogonalPolynomial (i : Fin N) : ℝ[X] :=
  M.changeOfMeasure (fun j : Fin N => X^j.val) i

/-- The corresponding orthonormal basis of the discrete L² model.
Use: multiplication by the node coordinate is expressed in this basis.
Article: jacobi, Appendix C.4 (gram–Cholesky reconstruction).
-/
def polynomialBasis : OrthonormalBasis (Fin N) ℝ (EuclideanSpace ℝ (Fin N)) :=
  Gram.basis (by simp) (fun j : Fin N => M.evaluate (X^j.val))

/-- The constructed polynomial has exactly the indexed degree and positive leading coefficient.
Use: fixes the Jacobi coupling orientation and the uniqueness normalization.
Article: jacobi, Appendix C.4 (gram–Cholesky reconstruction).
Proof: specialize the general change-of-measure theorem to monomials. -/
theorem orthogonalPolynomial_degree (i : Fin N) :
    (M.orthogonalPolynomial i).natDegree = i.val ∧
      0 < (M.orthogonalPolynomial i).leadingCoeff :=
  M.changeOfMeasure_degree _ (fun _ => by simp) (fun _ => by simp) i

/-- Weighted polynomial evaluation is precisely the canonical Gram--Schmidt basis vector.
Use: converts the multiplication matrix into weighted polynomial integrals.
Article: jacobi, Appendix C.4 (gram–Cholesky reconstruction).
Proof: specialize the polynomial evaluation formula for the inverse Cholesky transform. -/
theorem evaluate_orthogonalPolynomial (i : Fin N) :
    M.evaluate (M.orthogonalPolynomial i) = M.polynomialBasis i :=
  M.evaluate_changeOfMeasure _ (fun _ => by simp) (fun _ => by simp) i

/-- A lower-degree polynomial is orthogonal to every later canonical basis vector.
Use: proves tridiagonality of multiplication by x and identifies its adjacent coefficients.
Article: jacobi, Appendix C.4 (gram–Cholesky reconstruction).
Proof: expand the polynomial in monomials; Gram--Schmidt kills earlier degrees,
and the remaining monomial coefficients are zero by the degree bound. -/
theorem polynomialBasis_orthogonal_lower {p : ℝ[X]} {i : Fin N}
    (hp : p.natDegree < i.val) : inner ℝ (M.polynomialBasis i) (M.evaluate p) = 0 := by
  -- Expand in monomials; earlier degrees are orthogonal and later coefficients of the input polynomial vanish.
  have hpN : p.natDegree < N := hp.trans i.isLt
  have he : p = ∑ j : Fin N, p.coeff j.val • (X^j.val : ℝ[X]) := by
    rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => p.coeff j • (X^j : ℝ[X])) N]
    simpa only [smul_eq_C_mul] using p.as_sum_range_C_mul_X_pow' hpN
  change inner ℝ (M.polynomialBasis i) (M.evaluation p) = 0
  rw [he, map_sum]
  simp only [map_smul, inner_sum, inner_smul_right]
  apply Finset.sum_eq_zero
  intro j _
  by_cases hji : j < i
  · have hz := gramSchmidtOrthonormalBasis_inv_triangular
      (by simp : Module.finrank ℝ (EuclideanSpace ℝ (Fin N)) = Fintype.card (Fin N))
      (fun k : Fin N => M.evaluate (X^k.val)) hji
    rw [show inner ℝ (M.polynomialBasis i) (M.evaluation (X^j.val)) = 0 from hz, mul_zero]
  · rw [coeff_eq_zero_of_natDegree_lt (by omega), zero_mul]

/-- The canonical orthonormal polynomials are orthogonal in their actual discrete measure.
Use: supplies the recurrence and spectral weight calculations.
Article: jacobi, Appendix C.4 (gram–Cholesky reconstruction).
Proof: their evaluation vectors form the constructed orthonormal basis. -/
theorem orthogonalPolynomial_orthonormal :
    Orthonormal ℝ (fun i => M.evaluate (M.orthogonalPolynomial i)) := by
  simpa only [evaluate_orthogonalPolynomial] using M.polynomialBasis.orthonormal

end
end jacobi.Finite.DiscreteMeasure
