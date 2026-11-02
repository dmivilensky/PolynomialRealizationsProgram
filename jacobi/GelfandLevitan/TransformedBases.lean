import jacobi.GelfandLevitan.TransformedSynthesis

/-!
Article: jacobi, Appendix C.2 (two transformed orthonormal bases).
Both printed norming-weighted transformed systems are actual complete
orthonormal Hilbert bases of the original physical half-interval L2
space. The reference perturbation, compact Fredholm step, GL operator
factorization and frame identity have all been proved for the original
data before this unitary transport is constructed.
Use: transformedParityBasis constructs each complete original transformed basis without a completeness or orthogonality certificate input.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set jacobi.Reference
open scoped Topology InnerProductSpace
set_option backward.isDefEq.respectTransparency false

/-- The actual unitary transport from either original half-reference basis to its transformed parity family.
Use: transformedParityBasis constructs each complete original transformed basis without a completeness or orthogonality certificate input.
Article: jacobi, Proposition C.2.
-/
def transformedParityUnitary (a : ℝ) (ha : -1<a) (p : Fin 2) : halfSubspace ≃ₗᵢ[ℝ] halfSubspace :=
  Unitary.linearIsometryEquiv ⟨transformedSynthesis a ha p,transformedSynthesis_unitary a ha p⟩

/-- The two actual complete orthonormal bases of normalized original transformed waves.
Use: the midpoint boundary classification and the full reflected target operator in general Proposition C.2 use these same genuine half-interval bases.
Article: jacobi, Appendix C.2 (two transformed orthonormal bases).
-/
def transformedParityBasis (a : ℝ) (ha : -1<a) (p : Fin 2) : HilbertBasis ℕ ℝ halfSubspace :=
  HilbertBasis.ofRepr ((transformedParityUnitary a ha p).symm.trans (halfReferenceBasis a ha p).repr)

/-- Every entry of either actual transformed Hilbert basis is exactly the original norming-weighted u vector at its genuine target energy.
Use: all community Hilbert-basis orthogonality, expansion and completeness theorems now apply to the literal original functions in the midpoint and operator proof of general Proposition C.2.
Article: jacobi, Appendix C.2 (two transformed orthonormal bases).
Proof: the inverse of the transported coordinate unitary is the genuine synthesis unitary applied to the original reference expansion. Its independently proved actual basis image is exactly sqrt(2*c_k)*u_k. -/
theorem transformedParityBasis_apply (a : ℝ) (ha : -1<a) (p : Fin 2) (k : ℕ) :
    transformedParityBasis a ha p k=normalizedTransformedVector a ha (parityIndex p k) := by
  classical
  rw [← (transformedParityBasis a ha p).repr_symm_single k]
  unfold transformedParityBasis
  rw [LinearIsometryEquiv.symm_trans,LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.symm_symm,(halfReferenceBasis a ha p).repr_symm_single]
  exact transformedSynthesis_basis a ha p k

/-- Each original normalized transformed parity family has the exact Kronecker inner products of an orthonormal system.
Use: the actual transformed Green identity gives one common midpoint boundary condition in each original spectral parity class.
Article: jacobi, Appendix C.2 (two transformed orthonormal bases).
Proof: identify both actual vectors with the proved complete transformed Hilbert basis entries and use community orthonormality. -/
theorem normalizedTransformedVector_parity_inner (a : ℝ) (ha : -1<a) (p : Fin 2) (i j : ℕ) :
    inner ℝ (normalizedTransformedVector a ha (parityIndex p i))
      (normalizedTransformedVector a ha (parityIndex p j))=if i=j then 1 else 0 := by
  rw [← transformedParityBasis_apply a ha p i,← transformedParityBasis_apply a ha p j]
  exact (orthonormal_iff_ite.mp (transformedParityBasis a ha p).orthonormal) i j

/-- The original transformed waves at distinct indices of either genuine parity class are orthogonal on the physical half interval.
Use: the full original midpoint Green identity turns this exact orthogonality into collinearity of the genuine boundary states in Proposition C.2.
Article: jacobi, Appendix C.2 (two transformed orthonormal bases).
Proof: remove the original strictly positive norming factors from the independently proved normalized Kronecker inner products. -/
theorem transformedVector_parity_orthogonal (a : ℝ) (ha : -1<a) (p : Fin 2) {i j : ℕ} (hij : i≠j) :
    inner ℝ (transformedVector a ha (jacobi.Bessel.sigma a ha (parityIndex p i)))
      (transformedVector a ha (jacobi.Bessel.sigma a ha (parityIndex p j)))=0 := by
  -- Both normalizing scalars are the original positive square roots of the actual norming data.
  have h := normalizedTransformedVector_parity_inner a ha p i j
  rw [ite_eq_right hij,normalizedTransformedVector,normalizedTransformedVector,
    real_inner_smul_left
      (transformedVector a ha (jacobi.Bessel.sigma a ha (parityIndex p i)))
      ((halfNormalization a (parityIndex p j)*Real.sqrt (normingRatio a ha (parityIndex p j))) •
        transformedVector a ha (jacobi.Bessel.sigma a ha (parityIndex p j)))
      (halfNormalization a (parityIndex p i)*Real.sqrt (normingRatio a ha (parityIndex p i))),
    real_inner_smul_right
      (transformedVector a ha (jacobi.Bessel.sigma a ha (parityIndex p i)))
      (transformedVector a ha (jacobi.Bessel.sigma a ha (parityIndex p j)))
      (halfNormalization a (parityIndex p j)*Real.sqrt (normingRatio a ha (parityIndex p j)))] at h
  have hi : halfNormalization a (parityIndex p i)*Real.sqrt (normingRatio a ha (parityIndex p i))≠0 := by
    unfold halfNormalization
    positivity [(norming_pos ha (parityIndex p i)),(normingRatio_properties ha (parityIndex p i)).2]
  have hj : halfNormalization a (parityIndex p j)*Real.sqrt (normingRatio a ha (parityIndex p j))≠0 := by
    unfold halfNormalization
    positivity [(norming_pos ha (parityIndex p j)),(normingRatio_properties ha (parityIndex p j)).2]
  exact (mul_eq_zero.mp ((mul_eq_zero.mp h).resolve_left hi)).resolve_left hj

end
end jacobi.GelfandLevitan
