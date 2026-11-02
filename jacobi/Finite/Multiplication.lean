import jacobi.Finite.OrthogonalPolynomials
import jacobi.Finite.MatrixEncoding

/-!
Article: jacobi, Equation (1.3) (unique persymmetric realization and its weights).
Multiplication by the support coordinate in the constructed orthonormal
polynomial basis is symmetric tridiagonal with strictly positive adjacent
entries. The positivity is proved from the leading coefficients, not assumed.
Source: the finite Lanczos--Stieltjes reconstruction of de Boor and Golub.
Use: this is the reconstructed Jacobi matrix before coefficient encoding.
-/

namespace jacobi.Finite.DiscreteMeasure
noncomputable section
open chebyshev1 chebyshev2 Polynomial Matrix
open scoped BigOperators InnerProductSpace

variable {N : ℕ} (M : DiscreteMeasure N)

/-- Multiplication by x expressed in the actual orthonormal polynomial basis.
Use: this is the reconstructed Jacobi matrix before coefficient encoding.
Article: jacobi, Equation (1.3) (unique persymmetric realization and its weights).
-/
def multiplication : Matrix (Fin N) (Fin N) ℝ := fun i j =>
  inner ℝ (M.polynomialBasis i) (M.evaluate (X * M.orthogonalPolynomial j))

/-- The multiplication matrix is the weighted polynomial integral from the article.
Use: proves symmetry and relates its entries to the spectral weights.
Article: jacobi, Equation (1.3) (unique persymmetric realization and its weights).
Proof: substitute the weighted evaluations and the coordinate polynomial x. -/
theorem multiplication_integral (i j : Fin N) :
    M.multiplication i j = ∑ k, M.weight k * (M.orthogonalPolynomial i).eval (M.node k) *
      M.node k * (M.orthogonalPolynomial j).eval (M.node k) := by
  rw [multiplication, ← M.evaluate_orthogonalPolynomial i, M.inner_evaluate]
  apply Finset.sum_congr rfl
  intro k _
  simp only [eval_mul, eval_X]
  ring

/-- Multiplication is symmetric in the orthonormal polynomial basis.
Use: the constructed matrix is real Hermitian and its two adjacent diagonals agree.
Article: jacobi, Equation (1.3) (unique persymmetric realization and its weights).
Proof: each weighted scalar product is invariant under swapping the polynomials. -/
theorem multiplication_symmetric (i j : Fin N) : M.multiplication i j = M.multiplication j i := by
  rw [M.multiplication_integral, M.multiplication_integral]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- Entries beyond the adjacent diagonals vanish.
Use: supplies the tridiagonal hypotheses for the existing Jacobi coefficient encoding.
Article: jacobi, Equation (1.3) (unique persymmetric realization and its weights).
Proof: xψ_j has degree j+1 and is orthogonal to every later basis vector;
symmetry handles the opposite side of the diagonal. -/
theorem multiplication_tridiagonal (i j : Fin N)
    (hij : i.val+1 < j.val ∨ j.val+1 < i.val) : M.multiplication i j = 0 := by
  -- Multiplication raises degree by one, and orthogonality annihilates every more distant degree.
  have h (i j : Fin N) (hji : j.val+1 < i.val) : M.multiplication i j = 0 := by
    apply M.polynomialBasis_orthogonal_lower
    rw [natDegree_X_mul (leadingCoeff_ne_zero.mp (M.orthogonalPolynomial_degree j).2.ne'),
      (M.orthogonalPolynomial_degree j).1]
    exact hji
  rcases hij with hij | hji
  · rw [M.multiplication_symmetric]
    exact h j i hij
  · exact h i j hji

/-- The lower adjacent entry is the ratio of the two positive leading coefficients.
Use: proves strict positivity of every reconstructed coupling.
Article: jacobi, Equation (1.3) (unique persymmetric realization and its weights).
Proof: subtract the matching leading term from xψ_i. The remaining polynomial
has degree below j and hence zero pairing with ψ_j. -/
theorem multiplication_adjacent (i j : Fin N) (hij : i.val+1 = j.val) :
    M.multiplication j i =
      (M.orthogonalPolynomial i).leadingCoeff / (M.orthogonalPolynomial j).leadingCoeff := by
  -- Subtract the leading-coefficient ratio times the next polynomial; the remainder is lower degree.
  let qi := M.orthogonalPolynomial i
  let qj := M.orthogonalPolynomial j
  let c := qi.leadingCoeff / qj.leadingCoeff
  have hdi : qi.natDegree = i.val := (M.orthogonalPolynomial_degree i).1
  have hdj : qj.natDegree = j.val := (M.orthogonalPolynomial_degree j).1
  have hqj : qj.leadingCoeff ≠ 0 := (M.orthogonalPolynomial_degree j).2.ne'
  have hqi : qi ≠ 0 := leadingCoeff_ne_zero.mp (M.orthogonalPolynomial_degree i).2.ne'
  have hr : (X*qi-c • qj).natDegree ≤ i.val := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro k hk
    rw [coeff_sub, coeff_smul, smul_eq_mul]
    by_cases hkj : k = j.val
    · subst k
      rw [← hij, coeff_X_mul,
        show qi.coeff i.val = qi.leadingCoeff by rw [← hdi, coeff_natDegree],
        show qj.coeff (i.val+1) = qj.leadingCoeff by rw [hij, ← hdj, coeff_natDegree]]
      dsimp [c]
      rw [div_mul_cancel₀ _ hqj, sub_self]
    · rw [coeff_eq_zero_of_natDegree_lt (by rw [natDegree_X_mul hqi, hdi]; omega),
        coeff_eq_zero_of_natDegree_lt (by rw [hdj]; omega), mul_zero, sub_self]
  have hz := M.polynomialBasis_orthogonal_lower (i := j) (lt_of_le_of_lt hr (by omega))
  change inner ℝ (M.polynomialBasis j) (M.evaluation (X*qi-c • qj)) = 0 at hz
  rw [map_sub, map_smul, inner_sub_right, inner_smul_right] at hz
  have he : M.evaluation qj = M.polynomialBasis j := M.evaluate_orthogonalPolynomial j
  rw [he, M.polynomialBasis.inner_eq_one, mul_one] at hz
  exact sub_eq_zero.mp hz

/-- The constructed adjacent entries are strictly positive.
Use: establishes irreducibility, a conclusion of reconstruction rather than an input.
Article: jacobi, Equation (1.3) (unique persymmetric realization and its weights).
Proof: the adjacent coefficient is a ratio of positive leading coefficients. -/
theorem multiplication_adjacent_pos (i j : Fin N) (hij : i.val+1 = j.val) :
    0 < M.multiplication i j := by
  rw [M.multiplication_symmetric, M.multiplication_adjacent i j hij]
  exact div_pos (M.orthogonalPolynomial_degree i).2 (M.orthogonalPolynomial_degree j).2

/-- Encode the constructed multiplication matrix in the existing canonical Jacobi type.
Use: the inverse spectral-weight construction shares all finite and packing machinery.
Article: jacobi, Equation (1.3) (unique persymmetric realization and its weights).
-/
def reconstructed : Jacobi N := Finite.fromMatrix M.multiplication

/-- The coefficient matrix equals the constructed multiplication operator exactly.
Use: proves the reconstructed spectrum and spectral measure using finite linear algebra.
Article: jacobi, Equation (1.3) (unique persymmetric realization and its weights).
Proof: symmetry, tridiagonality and positive adjacent entries justify the encoding. -/
theorem reconstructed_matrix : M.reconstructed.matrix = M.multiplication := by
  apply Finite.fromMatrix_eq
  · exact Matrix.IsHermitian.ext (fun i j => by simpa using M.multiplication_symmetric j i)
  · exact fun i j hij => (M.multiplication_adjacent_pos i j hij).le
  · exact M.multiplication_tridiagonal

/-- Reconstruction yields positive internal squared couplings.
Use: the resulting matrix belongs to the irreducible, rather than reducible, fibre.
Article: jacobi, Equation (1.3) (unique persymmetric realization and its weights).
Proof: each encoded coupling is the square of a strictly positive adjacent entry. -/
theorem reconstructed_irreducible : M.reconstructed.Irreducible := by
  intro i hi hiN
  change 0 < if h : 0 < i ∧ i < N then
    (M.multiplication ⟨i-1, by omega⟩ ⟨i, h.2⟩)^2 else 0
  rw [dite_eq_left ⟨hi, hiN⟩]
  exact sq_pos_of_pos (M.multiplication_adjacent_pos _ _ (by dsimp; omega))

end
end jacobi.Finite.DiscreteMeasure
