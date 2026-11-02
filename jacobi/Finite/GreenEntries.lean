import jacobi.Finite.AnalyticChart

/-!
Article: jacobi, Theorem 2.1.
Every entry of the actual Green matrix has its original finite
spectral representation. This extends the existing diagonal identity
without changing the actual resolvent or eigenvector normalization.
Source: finite orthogonal spectral calculus, reused from chebyshev1.
Use: the actual persymmetric eigenvector limits and L1 spectral limit prove all pointwise Green-matrix limits of Theorem 2.1.
-/
namespace jacobi.Finite
noncomputable section
open chebyshev1 chebyshev2 Matrix

/-- The genuine Green matrix has the finite spectral representation
at every physical pair, including the off-diagonal entries.
Use: the actual persymmetric eigenvector limits and L1 spectral limit
prove all pointwise Green-matrix limits of Theorem 2.1.
Article: jacobi, Theorem 2.1.
Proof: conjugate the diagonal reciprocal spectral gaps back through
the original orthogonal basis and evaluate the actual matrix entry. -/
theorem green_entry_spectral {N:ℕ} (J:Jacobi N) (B:SpectralBasis J.matrix)
    (h:∀k,1-B.eigenvalues k≠0) (i j:Fin N) :
    J.green i j=∑k,B.Q i k*B.Q j k/(1-B.eigenvalues k) := by
  -- This is the same original inverse matrix, not a spectral definition of a new kernel.
  have he : J.green=B.Q*Matrix.diagonal (fun k => (1-B.eigenvalues k)⁻¹)*B.Qᵀ := by
    apply B.coordinates_injective
    rw [show B.coordinates J.green=Matrix.diagonal (fun k => (1-B.eigenvalues k)⁻¹) from
      SpectralCoordinates.coordinates_resolvent B h]
    simp only [SpectralBasis.coordinates,← Matrix.mul_assoc,B.transpose_mul,Matrix.one_mul]
    rw [Matrix.mul_assoc,B.transpose_mul,Matrix.mul_one]
  rw [he,Matrix.mul_apply]
  simp only [Matrix.mul_diagonal,Matrix.transpose_apply,div_eq_mul_inv]
  apply Finset.sum_congr rfl
  intro k _
  ring

end
end jacobi.Finite
