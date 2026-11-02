import jacobi.Finite.Multiplication

/-!
Article: jacobi, Equation (1.3) (unique persymmetric realization and its weights).
The constructed Jacobi matrix has exactly the input atoms as eigenvalues and
the input probabilities as its first-site spectral weights. The matrix and its
orthogonal diagonalization are constructed from the weighted polynomial basis.
Source: de Boor and Golub, finite inverse spectral reconstruction.
Use: diagonalizes the reconstructed Jacobi matrix in the prescribed atom order.
-/

namespace jacobi.Finite.DiscreteMeasure
noncomputable section
open chebyshev1 chebyshev2 Matrix Polynomial InnerProductSpace
open scoped BigOperators InnerProductSpace

variable {N : ℕ} (M : DiscreteMeasure N)

/-- Eigenvector matrix with polynomial-degree rows and support-point columns.
Use: diagonalizes the reconstructed Jacobi matrix in the prescribed atom order.
Article: jacobi, Equation (1.3) (unique persymmetric realization and its weights).
-/
def eigenvectors : Matrix (Fin N) (Fin N) ℝ := fun i k => M.polynomialBasis i k

/-- The rows of the constructed eigenvector matrix are orthonormal.
Use: obtains both inverse identities and the exact finite spectral basis.
Article: jacobi, Equation (1.3) (unique persymmetric realization and its weights).
Proof: the matrix row inner products are those of the orthonormal polynomial basis. -/
theorem eigenvectors_mul_transpose : M.eigenvectors * M.eigenvectorsᵀ = 1 := by
  ext i j
  have h := M.polynomialBasis.inner_eq_ite i j
  simpa [eigenvectors, Matrix.mul_apply, PiLp.inner_apply, Matrix.one_apply, mul_comm] using h

/-- The eigenvector matrix is also orthogonal on its columns.
Use: supplies the inverse used in the spectral reconstruction.
Article: jacobi, Equation (1.3) (unique persymmetric realization and its weights).
Proof: a square matrix right inverse is a left inverse. -/
theorem eigenvectors_transpose_mul : M.eigenvectorsᵀ * M.eigenvectors = 1 :=
  mul_eq_one_comm.mp M.eigenvectors_mul_transpose

/-- Multiplication is conjugate to the diagonal matrix of the input atoms.
Use: proves the reconstructed characteristic polynomial and its complete spectrum.
Article: jacobi, Equation (1.3) (unique persymmetric realization and its weights).
Proof: evaluate xψ_j at every atom and expand the Euclidean inner product. -/
theorem multiplication_diagonalization :
    M.multiplication = M.eigenvectors * Matrix.diagonal M.node * M.eigenvectorsᵀ := by
  -- The polynomial evaluation formula turns each spectral sum into the multiplication inner product.
  ext i j
  have he := M.evaluate_orthogonalPolynomial j
  rw [Matrix.mul_apply]
  simp only [multiplication, Matrix.mul_diagonal, Matrix.transpose_apply,
    eigenvectors, PiLp.inner_apply, Real.inner_apply]
  apply Finset.sum_congr rfl
  intro k _
  have hk := congrArg (fun v : EuclideanSpace ℝ (Fin N) => v k) he
  change Real.sqrt (M.weight k) * (M.orthogonalPolynomial j).eval (M.node k) =
    M.polynomialBasis j k at hk
  change (M.polynomialBasis i k) *
    (Real.sqrt (M.weight k) * (X * M.orthogonalPolynomial j).eval (M.node k)) = _
  rw [eval_mul, eval_X]
  calc
    _ = M.polynomialBasis i k * M.node k *
        (Real.sqrt (M.weight k) * (M.orthogonalPolynomial j).eval (M.node k)) := by ring
    _ = _ := by rw [hk]

/-- Actual orthogonal spectral data of the constructed Jacobi matrix.
Use: all existing spectral weight and resolvent theorems apply to this reconstruction.
Article: jacobi, Equation (1.3) (unique persymmetric realization and its weights).
-/
def reconstructedBasis : SpectralBasis M.reconstructed.matrix where
  Q := M.eigenvectors
  eigenvalues := M.node
  transpose_mul := M.eigenvectors_transpose_mul
  mul_transpose := M.eigenvectors_mul_transpose
  diagonalize := by
    rw [M.reconstructed_matrix, M.multiplication_diagonalization]
    simp only [← Matrix.mul_assoc, M.eigenvectors_transpose_mul, Matrix.one_mul]
    rw [Matrix.mul_assoc, M.eigenvectors_transpose_mul, Matrix.mul_one]

/-- The reconstructed terminal polynomial has exactly the prescribed support points.
Use: proves existence in every arbitrary simple-root fibre.
Article: jacobi, Equation (1.3) (unique persymmetric realization and its weights).
Proof: use the explicitly constructed orthogonal spectral basis. -/
theorem reconstructed_charpoly :
    M.reconstructed.matrix.charpoly = ∏ i, (X-C (M.node i)) :=
  M.reconstructedBasis.charpoly_factor

/-- The first polynomial basis vector is the weighted constant polynomial.
Use: identifies the first-site spectral weights as exactly the prescribed probabilities.
Article: jacobi, Equation (1.3) (unique persymmetric realization and its weights).
Proof: Gram--Schmidt leaves the first monomial unchanged, and probability mass one
gives that vector unit norm. -/
theorem polynomialBasis_first (hN : 0 < N) :
    M.polynomialBasis ⟨0, hN⟩ = M.evaluate 1 := by
  -- The first monomial is the constant polynomial, whose weighted evaluation has norm one.
  let : NeZero N := ⟨hN.ne'⟩
  have hf := M.evaluate_linearIndependent (fun i : Fin N => (X^i.val : ℝ[X]))
    (fun _ => by simp) (fun _ => by simp)
  have hnormsq : ‖M.evaluate 1‖^2 = 1 := by
    rw [← real_inner_self_eq_norm_sq, M.inner_evaluate]
    simpa using M.probability
  have hnorm : ‖M.evaluate 1‖ = 1 := by nlinarith [norm_nonneg (M.evaluate 1)]
  have hg : gramSchmidt ℝ (fun i : Fin N => M.evaluate (X^i.val)) (0 : Fin N) =
      M.evaluate 1 := by
    rw [gramSchmidt_def]
    have hz : Finset.Iio (0 : Fin N) = ∅ := by ext k; simp
    simp only [hz, Finset.sum_empty, sub_zero, Fin.val_zero, pow_zero]
  change Gram.basis _ _ (0 : Fin N) = _
  rw [Gram.basis, gramSchmidtOrthonormalBasis_apply _
    ((gramSchmidtNormed_linearIndependent hf).ne_zero (0 : Fin N))]
  simp only [gramSchmidtNormed, hg, hnorm, RCLike.ofReal_real_eq_id, id_eq, inv_one, one_smul]

/-- The first coordinate of each eigenvector is the positive square root of its input weight.
Use: both positivity and the exact spectral measure follow from this identity.
Article: jacobi, Equation (1.3) (unique persymmetric realization and its weights).
Proof: evaluate the unit constant polynomial at the support point. -/
theorem eigenvectors_first (hN : 0 < N) (k : Fin N) :
    M.eigenvectors ⟨0, hN⟩ k = Real.sqrt (M.weight k) := by
  rw [eigenvectors, M.polynomialBasis_first hN]
  simp [evaluate]

/-- Reconstruction realizes every positive spectral probability vector exactly.
Use: the existence direction of the open-simplex spectral parametrization.
Article: jacobi, Equation (1.3) (unique persymmetric realization and its weights).
Proof: square the positive first eigenvector coordinate. -/
theorem reconstructed_weight (hN : 0 < N) (k : Fin N) :
    M.reconstructedBasis.weight ⟨0, hN⟩ k = M.weight k := by
  change M.eigenvectors ⟨0, hN⟩ k^2 = M.weight k
  rw [M.eigenvectors_first hN, Real.sq_sqrt (M.positive k).le]

end
end jacobi.Finite.DiscreteMeasure
