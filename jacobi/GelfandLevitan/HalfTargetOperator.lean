import jacobi.GelfandLevitan.TransformedBases
import chebyshev2.Continuum.UnboundedDiagonal

/-!
Article: jacobi, Appendix C.2.
Each actual transformed half-interval basis gives a genuine positive
self-adjoint unbounded operator on its full weighted-square graph
domain. Its eigenvalues and eigenvectors are the original sigma_k and
normalized u_k. This is the half-interval spectral realization used
before the two classes are joined at the physical midpoint.
Use: the full target operator in Proposition C.2 joins these two genuine spectral realizations through the proved transformed eigenfunctions and their midpoint boundary conditions.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set jacobi.Reference
open scoped Topology InnerProductSpace

/-- The actual target spectral operator in either physical half-interval parity class, on its full unbounded graph domain.
Use: the full target operator in Proposition C.2 joins these two genuine spectral realizations through the proved transformed eigenfunctions and their midpoint boundary conditions.
Article: jacobi, Appendix C.2.
-/
def halfTargetOperator (a : ℝ) (ha : -1<a) (p : Fin 2) : halfSubspace →ₗ.[ℝ] halfSubspace :=
  chebyshev2.Continuum.unboundedDiagonalOperator (transformedParityBasis a ha p)
    (fun k => jacobi.Bessel.sigma a ha (parityIndex p k))

/-- The original half target operator domain is exactly the full weighted-square summability domain of its actual transformed basis coefficients.
Use: makes the genuine self-adjoint realization explicit before the midpoint gluing in general Proposition C.2.
Article: jacobi, Proposition C.2.
Proof: specialize the earlier article's proved unbounded diagonal domain characterization to the actual transformed Hilbert basis and original sigma enumeration. -/
theorem halfTargetOperator_domain (a : ℝ) (ha : -1<a) (p : Fin 2) (v : halfSubspace) :
    v∈(halfTargetOperator a ha p).domain ↔
      Summable (fun k => (jacobi.Bessel.sigma a ha (parityIndex p k))^2*
        ((transformedParityBasis a ha p).repr v k)^2) :=
  chebyshev2.Continuum.unboundedDiagonalDomain_iff _ _ _

/-- Each genuine half target spectral operator is self-adjoint for the community unbounded adjoint on the original Hilbert space.
Use: supplies the two actual half spectral realizations in the full target operator statement of Proposition C.2.
Article: jacobi, Proposition C.2.
Proof: apply the earlier fully proved unbounded diagonal self-adjointness theorem to the actual complete transformed basis and real original spectrum. -/
theorem halfTargetOperator_selfAdjoint (a : ℝ) (ha : -1<a) (p : Fin 2) :
    (halfTargetOperator a ha p).adjoint=halfTargetOperator a ha p :=
  chebyshev2.Continuum.unboundedDiagonalOperator_selfAdjoint _ _

/-- Each actual half target operator has dense full graph domain.
Use: these are genuine densely defined self-adjoint operators for the spectral realization in general Proposition C.2.
Article: jacobi, Proposition C.2.
Proof: reuse the earlier article's genuine unbounded diagonal density theorem for the actual transformed Hilbert basis. -/
theorem halfTargetOperator_dense (a : ℝ) (ha : -1<a) (p : Fin 2) :
    Dense ((halfTargetOperator a ha p).domain : Set halfSubspace) :=
  chebyshev2.Continuum.unboundedDiagonalDomain_dense _ _

/-- Every actual original transformed basis entry lies in the full half target operator domain.
Use: halfTargetOperator_basis records the actual target eigenvalue equation on the genuine original eigenfunctions.
Article: jacobi, Proposition C.2.
Proof: the earlier diagonal graph contains every genuine basis vector. -/
theorem halfTargetOperator_basis_mem (a : ℝ) (ha : -1<a) (p : Fin 2) (k : ℕ) :
    transformedParityBasis a ha p k∈(halfTargetOperator a ha p).domain :=
  chebyshev2.Continuum.unboundedDiagonalDomain_basis _ _ _

/-- Each actual original normalized transformed basis entry has its genuine sigma eigenvalue under the half target operator.
Use: the full target realization of Proposition C.2 retains exactly these actual eigenfunctions and eigenvalues after midpoint gluing.
Article: jacobi, Proposition C.2.
Proof: apply the earlier article's genuine diagonal eigenvector theorem. TransformedBases identifies each basis entry with the original sqrt(2*c_k)*u_k, so this concerns the actual transformed functions. -/
theorem halfTargetOperator_basis (a : ℝ) (ha : -1<a) (p : Fin 2) (k : ℕ) :
    halfTargetOperator a ha p ⟨transformedParityBasis a ha p k,halfTargetOperator_basis_mem a ha p k⟩=
      jacobi.Bessel.sigma a ha (parityIndex p k) • transformedParityBasis a ha p k :=
  chebyshev2.Continuum.unboundedDiagonalOperator_basis _ _ _

/-- The genuine half target operators are nonnegative on their full original unbounded domains.
Use: supplies the actual positive half spectral realizations in general Proposition C.2, using the true Bessel spectrum rather than the reference tau spectrum.
Article: jacobi, Proposition C.2.
Proof: every original sigma is a genuine positive Bessel spectral zero. The earlier full-domain diagonal positivity theorem therefore applies to these actual eigenvalues and transformed bases. -/
theorem halfTargetOperator_nonnegative (a : ℝ) (ha : -1<a) (p : Fin 2)
    (v : (halfTargetOperator a ha p).domain) :
    0 ≤ inner ℝ (halfTargetOperator a ha p v) (v:halfSubspace) :=
  chebyshev2.Continuum.unboundedDiagonalOperator_nonnegative _ _
    (fun k => (jacobi.Bessel.spectralZero_pos ha (jacobi.Bessel.sigma_mem ha (parityIndex p k))).le) v

end
end jacobi.GelfandLevitan
