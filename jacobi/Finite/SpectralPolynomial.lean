import jacobi.Finite.Basic
import chebyshev1.Jacobi.Orthogonality

/-!
Article: jacobi, Appendix C.3 (complex edge-wave convergence).
Use: spectral_coordinates_aeval reuses the community polynomial functoriality theorem for the already constructed original ordered basis.
-/
namespace jacobi.Finite
noncomputable section
open Matrix Polynomial chebyshev1 chebyshev2
set_option backward.isDefEq.respectTransparency false

/-- Conjugation by the genuine original finite spectral basis as an actual real algebra homomorphism.
Use: spectral_coordinates_aeval reuses the community polynomial functoriality theorem for the already constructed original ordered basis.
Article: jacobi, Appendix C.3 (complex edge-wave convergence).
Source: finite spectral conjugation and mathlib Polynomial.aeval_algHom_apply.
Proof: the existing original coordinate map preserves multiplication by its proved two-sided basis inverse. Its original scalar and additive formulas follow by actual matrix multiplication. -/
def spectralCoordinatesAlgHom {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (B : SpectralBasis A) :
    Matrix (Fin n) (Fin n) ℝ →ₐ[ℝ] Matrix (Fin n) (Fin n) ℝ where
  toFun := B.coordinates
  map_zero' := by simp [SpectralBasis.coordinates]
  map_one' := by simp [SpectralBasis.coordinates,B.transpose_mul]
  map_add' U V := by simp [SpectralBasis.coordinates,Matrix.mul_add,Matrix.add_mul]
  map_mul' U V := B.coordinates_mul U V
  commutes' c := by
    simp only [SpectralBasis.coordinates,Algebra.algebraMap_eq_smul_one,Matrix.mul_smul,
      Matrix.mul_one,smul_mul_assoc,B.transpose_mul]

/-- Every polynomial in the actual original matrix has its exact original eigenvalue polynomial in any genuine original ordered spectral coordinates.
Use: spectral_leading_values transports the already proved original leading-site identity to the actual original support polynomial values.
Article: jacobi, Appendix C.3 (complex edge-wave convergence).
Source: mathlib polynomial algebra-homomorphism functoriality and the reused original diagonal evaluation theorem.
Proof: apply polynomial functoriality to the genuine original conjugation algebra homomorphism and its independently proved actual diagonalization. -/
theorem spectral_coordinates_aeval {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (B : SpectralBasis A)
    (p : ℝ[X]) : B.coordinates (aeval A p)=Matrix.diagonal (fun k => p.eval (B.eigenvalues k)) := by
  have h := Polynomial.aeval_algHom_apply (spectralCoordinatesAlgHom B) A p
  change aeval (B.coordinates A) p=B.coordinates (aeval A p) at h
  rw [show B.coordinates A=Matrix.diagonal B.eigenvalues from B.diagonalize,aeval_diagonal] at h
  exact h.symm

/-- The original polynomial matrix intertwines the genuine spectral transpose with its exact original diagonal polynomial values.
Use: spectral_leading_values evaluates the actual original leading-site identity at each genuine spectral coordinate.
Article: jacobi, Appendix C.3 (complex edge-wave convergence).
Proof: multiply the proved actual spectral-coordinate polynomial identity by the genuine original spectral transpose and cancel the proved original basis inverse. -/
theorem spectral_polynomial_intertwine {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (B : SpectralBasis A)
    (p : ℝ[X]) : B.Q.transpose*aeval A p=
      Matrix.diagonal (fun k => p.eval (B.eigenvalues k))*B.Q.transpose := by
  have h := congrArg (fun M:Matrix (Fin n) (Fin n) ℝ => M*B.Q.transpose) (spectral_coordinates_aeval B p)
  change (B.Q.transpose*aeval A p*B.Q)*B.Q.transpose=_ at h
  simpa only [Matrix.mul_assoc,B.mul_transpose,Matrix.mul_one] using h

/-- The actual original leading recurrence polynomial has its precise signed spectral value at every genuine original eigenvector entry.
Use: normalizedLeading_eq_orthogonalPolynomial identifies the original support recurrence functions with the same actual canonical orthogonal polynomials used by the finite Gram transformation.
Article: jacobi, Appendix C.3 (positive coefficients, persymmetry and spectrum).
Proof: reuse the earlier exact original leading polynomial applied to the first-site vector. The genuine polynomial intertwining sends this same physical column to its actual eigenvalue values. Its singleton-supported right side recovers exactly the original m-th spectral row, retaining its sign and true coupling-product normalization. -/
theorem spectral_leading_values {n : ℕ} (J : Jacobi n) (B : SpectralBasis J.matrix) (hn:0<n)
    {s : ℕ} (hs:s<n) (k:Fin n) :
    (J.data.leading s).eval (B.eigenvalues k)*B.Q ⟨0,hn⟩ k=
      J.data.linkProduct s*B.Q ⟨s,hs⟩ k := by
  -- The original physical first column has already been computed in the earlier article; here only its genuine spectral coordinates are taken.
  have hcol (i:Fin n) : (aeval J.matrix (J.data.leading s)) i ⟨0,hn⟩=
      J.data.linkProduct s*JacobiData.site n s i := by
    have h := J.data.leading_aeval_site n s hn hs J.coupling_nonneg
    rw [JacobiData.site_eq_single n 0 hn,Matrix.mulVec_single_one] at h
    exact congrArg (fun v:Fin n → ℝ => v i) h
  have h := congrArg (fun M:Matrix (Fin n) (Fin n) ℝ => M k ⟨0,hn⟩)
    (spectral_polynomial_intertwine B (J.data.leading s))
  simp only [Matrix.diagonal_mul] at h
  simp only [Matrix.mul_apply,Matrix.transpose_apply] at h
  simp_rw [hcol] at h
  rw [JacobiData.site_eq_single n s hs] at h
  simp only [Pi.single_apply,mul_ite,mul_zero,mul_one,
    Finset.sum_ite_eq',Finset.mem_univ,ite_true] at h
  nlinarith [h]

end
end jacobi.Finite
