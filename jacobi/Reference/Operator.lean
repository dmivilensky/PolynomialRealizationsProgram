import jacobi.Reference.HilbertBasis
import jacobi.Reference.EigenEquation
import jacobi.Reference.Endpoint
import chebyshev2.Continuum.UnboundedDiagonal

/-!
Article: jacobi, Appendix C.1.
The original reference eigenfunctions form a complete actual Hilbert
basis. The general unbounded-diagonal construction of chebyshev2
therefore gives the reference self-adjoint operator on its full weighted
ell2 graph domain, with every source eigenvalue and the selected regular
branch. No positivity assumption on the reference spectrum is imposed.
Use: supplies the complete self-adjoint reference spectral realization for midpoint splitting and the GL transformation of Proposition C.2.
-/
namespace jacobi.Reference
noncomputable section
open Real Set MeasureTheory
attribute [local instance] Measure.Subtype.measureSpace

/-- The actual source reference operator on its full unbounded spectral graph domain.
Use: supplies the complete self-adjoint reference spectral realization for midpoint splitting and the GL transformation of Proposition C.2.
Article: jacobi, Appendix C.1.
-/
def referenceOperator (a : ℝ) (ha : -1<a) : Space →ₗ.[ℝ] Space :=
  chebyshev2.Continuum.unboundedDiagonalOperator (hilbertBasis a ha) (eigenvalue a)

/-- The genuine reference operator domain is exactly the full original weighted ell2 graph domain.
Use: specifies the reference realization explicitly and supports subsequent operator and resolvent arguments.
Article: jacobi, Appendix C.1.
Proof: specialize the proved general unbounded-diagonal graph characterization from the earlier article. -/
theorem referenceOperator_domain (a : ℝ) (ha : -1<a) (u : Space) :
    u∈(referenceOperator a ha).domain ↔
      Summable (fun k => (eigenvalue a k)^2*((hilbertBasis a ha).repr u k)^2) :=
  chebyshev2.Continuum.unboundedDiagonalDomain_iff _ _ _

/-- The actual reference operator is genuinely self-adjoint using mathlib's adjoint of an unbounded operator.
Use: supplies the operator-level reference premise of the source's full continuum construction, rather than only a symmetric differential expression.
Article: jacobi, Appendix C.1.
Proof: the earlier article's complete unbounded diagonal self-adjointness theorem applies to the genuine reference Hilbert basis and real source eigenvalues. -/
theorem referenceOperator_selfAdjoint (a : ℝ) (ha : -1<a) :
    (referenceOperator a ha).adjoint=referenceOperator a ha :=
  chebyshev2.Continuum.unboundedDiagonalOperator_selfAdjoint _ _

/-- The actual reference operator has a dense domain in the entire original Lebesgue Hilbert space.
Use: establishes a genuine densely defined self-adjoint reference realization for the operator transformation.
Article: jacobi, Appendix C.1.
Proof: the complete actual reference basis has all its finite combinations in the full diagonal graph domain. -/
theorem referenceOperator_dense (a : ℝ) (ha : -1<a) : Dense ((referenceOperator a ha).domain : Set Space) :=
  chebyshev2.Continuum.unboundedDiagonalDomain_dense _ _

/-- Every genuine reference basis vector belongs to the full original reference graph domain.
Use: fixes actual reference eigenvectors for midpoint splitting and the differential realization.
Article: jacobi, Appendix C.1.
Proof: the general diagonal graph contains every basis vector, since its coefficient support is a singleton. -/
theorem referenceOperator_basis_mem (a : ℝ) (ha : -1<a) (k : ℕ) :
    hilbertBasis a ha k∈(referenceOperator a ha).domain :=
  chebyshev2.Continuum.unboundedDiagonalDomain_basis _ _ _

/-- The actual reference operator has precisely the original source eigenvalues on its genuine normalized reference basis.
Use: identifies the unbounded operator with the original reference spectral data before the GL transformation.
Article: jacobi, Appendix C.1.
Proof: specialize the earlier genuine unbounded-diagonal eigenvector theorem to the actual complete reference basis. -/
theorem referenceOperator_basis (a : ℝ) (ha : -1<a) (k : ℕ) :
    referenceOperator a ha ⟨hilbertBasis a ha k,referenceOperator_basis_mem a ha k⟩=
      eigenvalue a k • hilbertBasis a ha k :=
  chebyshev2.Continuum.unboundedDiagonalOperator_basis _ _ _

/-- The actual complete normalized reference basis consists of the source's classical Schrodinger eigenfunctions with its selected endpoint branch.
Use: ties the genuine reference self-adjoint spectral construction to the original differential equation, including the gamma<1/2 branch.
Article: jacobi, Lemma C.1.
Proof: combine the proved original function representative, exact true differential equation and normalized selected-branch endpoint limit. -/
theorem reference_basis_identification (a : ℝ) (ha : -1<a) (k : ℕ) :
    (hilbertBasis a ha k=ᵐ[volume] fun t : Interval => eigenfunction a k t/Real.sqrt (norming a k)) ∧
      (∀ t∈Ioo (0:ℝ) 1,-eigenfunctionAcceleration a k t+potential a t*eigenfunction a k t=
        eigenvalue a k*eigenfunction a k t) ∧
      Filter.Tendsto (fun t => eigenfunction a k t/t^(gamma a)) (nhdsWithin 0 (Ioi 0)) (nhds 1) :=
  ⟨hilbertBasis_ae a ha k,fun _ ht => eigenfunction_equation ha k ht,eigenfunction_endpoint_limit a k⟩

end
end jacobi.Reference
