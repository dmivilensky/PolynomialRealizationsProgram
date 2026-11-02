import jacobi.GelfandLevitan.FullTransformedBasis
import chebyshev2.Continuum.UnboundedDiagonal

/-!
Article: jacobi, Theorem 2.1.
The full H_alpha is the genuine self-adjoint spectral operator on the
original full-interval L2 space, with its full weighted-square domain
and the original reflected u_k eigenbasis. Its physical differential
identification additionally requires midpoint boundary matching.
Use: targetGreenOperator is its actual bounded inverse; the midpoint differential argument identifies its action on finite original spectral combinations with the printed Schrodinger expression.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set jacobi.Reference
open scoped Topology InnerProductSpace

/-- The genuine full original target spectral operator H_alpha.
Use: targetGreenOperator is its actual bounded inverse; the midpoint differential argument identifies its action on finite original spectral combinations with the printed Schrodinger expression.
Article: jacobi, Theorem 2.1.
-/
def targetOperator (a : ℝ) (ha : -1<a) : Space →ₗ.[ℝ] Space :=
  chebyshev2.Continuum.unboundedDiagonalOperator (fullTargetBasis a ha) (jacobi.Bessel.sigma a ha)

/-- The full original target operator domain is exactly the weighted-square summability domain of its actual reflected transformed coefficients.
Use: targetGreen_mem and the physical differential realization use the full spectral graph domain rather than only finite combinations.
Article: jacobi, Theorem 2.1.
Proof: specialize the earlier article's proved unbounded diagonal domain characterization to the actual full target basis and original sigma enumeration. -/
theorem targetOperator_domain (a : ℝ) (ha : -1<a) (v : Space) :
    v∈(targetOperator a ha).domain ↔
      Summable (fun k => (jacobi.Bessel.sigma a ha k)^2*((fullTargetBasis a ha).repr v k)^2) :=
  chebyshev2.Continuum.unboundedDiagonalDomain_iff _ _ _

/-- The full original target spectral operator is genuinely self-adjoint on the actual physical L2 space.
Use: the complete operator assertion in Proposition C.2 uses the true community unbounded adjoint.
Article: jacobi, Theorem 2.1.
Proof: reuse the earlier article's complete unbounded diagonal self-adjointness theorem for the independently proved original full target Hilbert basis. -/
theorem targetOperator_selfAdjoint (a : ℝ) (ha : -1<a) :
    (targetOperator a ha).adjoint=targetOperator a ha :=
  chebyshev2.Continuum.unboundedDiagonalOperator_selfAdjoint _ _

/-- The full original target spectral realization has dense domain.
Use: supplies the genuine densely defined self-adjoint realization and inverse identities of Proposition C.2.
Article: jacobi, Theorem 2.1.
Proof: the earlier diagonal density theorem applies to the actual complete full basis. -/
theorem targetOperator_dense (a : ℝ) (ha : -1<a) :
    Dense ((targetOperator a ha).domain : Set Space) :=
  chebyshev2.Continuum.unboundedDiagonalDomain_dense _ _

/-- Each original full reflected transformed basis vector belongs to the full target operator graph domain.
Use: targetOperator_basis fixes the actual original eigenvectors, and finite spectral combinations inherit this domain membership.
Article: jacobi, Theorem 2.1.
Proof: every actual basis vector belongs to the earlier unbounded diagonal domain. -/
theorem targetOperator_basis_mem (a : ℝ) (ha : -1<a) (k : ℕ) :
    fullTargetBasis a ha k∈(targetOperator a ha).domain :=
  chebyshev2.Continuum.unboundedDiagonalDomain_basis _ _ _

/-- The full target realization has the genuine original sigma_k eigenvalues on the actual original reflected transformed functions.
Use: targetGreenOperator and the physical differential identification use the same original spectral data and eigenfunctions.
Article: jacobi, Theorem 2.1.
Proof: specialize the earlier article's actual unbounded diagonal eigenvector theorem to the proved full original transformed basis. -/
theorem targetOperator_basis (a : ℝ) (ha : -1<a) (k : ℕ) :
    targetOperator a ha ⟨fullTargetBasis a ha k,targetOperator_basis_mem a ha k⟩=
      jacobi.Bessel.sigma a ha k • fullTargetBasis a ha k :=
  chebyshev2.Continuum.unboundedDiagonalOperator_basis _ _ _

/-- The full original target spectral operator is nonnegative on its entire original unbounded domain.
Use: the genuine bounded Green inverse and the strictly positive sigma spectrum give the positive target realization of Proposition C.2.
Article: jacobi, Theorem 2.1.
Proof: every original sigma_k is strictly positive; apply the earlier full-domain diagonal nonnegativity theorem to the actual full target basis. -/
theorem targetOperator_nonnegative (a : ℝ) (ha : -1<a) (v : (targetOperator a ha).domain) :
    0 ≤ inner ℝ (targetOperator a ha v) (v:Space) :=
  chebyshev2.Continuum.unboundedDiagonalOperator_nonnegative _ _
    (fun k => (jacobi.Bessel.spectralZero_pos ha (jacobi.Bessel.sigma_mem ha k)).le) v

end
end jacobi.GelfandLevitan
