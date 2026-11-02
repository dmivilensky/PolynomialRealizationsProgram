import jacobi.Finite.Affine
import chebyshev1.Spectral.Weights

/-!
Article: jacobi, Appendix C.3 (positive coefficients, persymmetry and spectrum).
The genuine original finite spectral basis survives a positive affine
change of its Jacobi matrix. The actual eigenvectors and spectral weights
remain unchanged and the actual eigenvalues have their literal affine
images, without imposing contractivity on the transformed spectrum.
Use: Support.supportBasis identifies the literal original corrected support spectrum and unchanged original spectral weights.
-/
namespace jacobi.Finite
noncomputable section
open Matrix Polynomial chebyshev1 chebyshev2

/-- The genuine spectral basis of the actual affine finite Jacobi transformation, retaining the original physical eigenvectors.
Use: Support.supportBasis identifies the literal original corrected support spectrum and unchanged original spectral weights.
Article: jacobi, Appendix C.3 (positive coefficients, persymmetry and spectrum).
Source: the finite real spectral theorem under an affine transformation.
Proof: keep the genuine original orthogonal basis matrix. Its two inverse identities are unchanged, and linearity of the actual conjugation sends c*J+d*I to diag(c*lambda_k+d). -/
def affineBasis {n : ℕ} (J : Jacobi n) (B : SpectralBasis J.matrix) {c : ℝ} (hc : 0≤c) (d : ℝ) :
    SpectralBasis (affine J c d).matrix where
  Q := B.Q
  eigenvalues k := c*B.eigenvalues k+d
  transpose_mul := B.transpose_mul
  mul_transpose := B.mul_transpose
  diagonalize := by
    -- This is an exact original finite conjugation; no transformed eigenbasis is postulated.
    rw [affine_matrix J hc d]
    have hs : Matrix.scalar (Fin n) d=d • (1:Matrix (Fin n) (Fin n) ℝ) := by
      ext i j
      simp only [Matrix.scalar_apply,Matrix.diagonal_apply,Matrix.smul_apply,Matrix.one_apply,smul_eq_mul]
      split_ifs <;> ring
    rw [hs,Matrix.mul_add,Matrix.add_mul,Matrix.mul_smul,smul_mul_assoc,
      Matrix.mul_smul,Matrix.mul_one,smul_mul_assoc,B.diagonalize,B.transpose_mul]
    ext i j
    simp only [Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,Matrix.diagonal_apply,Matrix.one_apply]
    split_ifs <;> ring

/-- Every actual finite affine spectral eigenvalue is exactly its original affine node image.
Use: the support chain spectrum is precisely the article's original corrected model lattice eta_(n,k).
Article: jacobi, Appendix C.3 (complex edge-wave convergence).
Proof: the original affine spectral construction preserves the genuine eigenvalue labels. -/
theorem affineBasis_values {n : ℕ} (J : Jacobi n) (B : SpectralBasis J.matrix) {c : ℝ} (hc : 0≤c)
    (d : ℝ) (k : Fin n) : (affineBasis J B hc d).eigenvalues k=c*B.eigenvalues k+d := rfl

/-- Every actual affine finite spectral weight equals the genuine original spectral weight at the same physical and spectral indices.
Use: the support measure and its original polynomial system keep the same weights before and after the source's affine correction.
Article: jacobi, Appendix C.3 (askey–Wilson comparison chain).
Proof: the actual affine basis retains exactly the original orthogonal eigenvector matrix, whose squared entries define the genuine original weights. -/
theorem affineBasis_weight {n : ℕ} (J : Jacobi n) (B : SpectralBasis J.matrix) {c : ℝ} (hc : 0≤c)
    (d : ℝ) (i k : Fin n) : (affineBasis J B hc d).weight i k=B.weight i k := rfl

end
end jacobi.Finite
