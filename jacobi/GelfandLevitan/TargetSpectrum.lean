import jacobi.GelfandLevitan.TargetReflection

/-!
Article: jacobi, Theorem 2.1.
The actual full spectral operator has exactly the original sigma_k
eigenvalues, every eigenspace is one-dimensional, and its quadratic
form is strictly positive on every nonzero vector in the full domain.
Use: targetOperator_eigenvalue_iff and targetOperator_strictPositive obtain an actual original spectral index from any nonzero input.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set jacobi.Reference
open scoped Topology InnerProductSpace
set_option backward.isDefEq.respectTransparency false

/-- A nonzero full physical vector has a nonzero coefficient in the actual complete original target basis.
Use: targetOperator_eigenvalue_iff and targetOperator_strictPositive obtain an actual original spectral index from any nonzero input.
Article: jacobi, Theorem 2.1.
Source: injectivity of Hilbert basis coordinates.
Proof: if every coordinate vanished, the actual coordinate isometry would identify the vector with zero. -/
theorem target_nonzero_coordinate (a : ℝ) (ha : -1<a) {v : Space} (hv : v≠0) :
    ∃ k,(fullTargetBasis a ha).repr v k≠0 := by
  -- Completeness identifies a vector with zero if all its original spectral coordinates vanish.
  by_contra h
  push Not at h
  apply hv
  apply (fullTargetBasis a ha).repr.injective
  apply lp.ext
  apply funext
  intro k
  rw [h k,map_zero]
  rfl

/-- The eigenvalues of the genuine full target operator are exactly the original enumerated sigma_k, with no additional eigenvalue assumptions.
Use: the full target spectral identification of Proposition C.2 refers to the actual unbounded operator and its complete genuine eigenbasis.
Article: jacobi, Theorem 2.1.
Proof: at a nonzero coordinate of an actual eigenvector, its true graph equation cancels the nonzero coordinate and identifies its eigenvalue with sigma_k. Conversely every genuine original basis entry is an eigenvector of norm one. -/
theorem targetOperator_eigenvalue_iff (a : ℝ) (ha : -1<a) (E : ℝ) :
    (∃ v:(targetOperator a ha).domain,(v:Space)≠0 ∧ targetOperator a ha v=E • (v:Space)) ↔
      ∃ k,E= jacobi.Bessel.sigma a ha k := by
  -- The graph domain is the full weighted-square domain of the original reflected transformed basis.
  constructor
  · rintro ⟨v,hv,hE⟩
    obtain ⟨k,hk⟩ := target_nonzero_coordinate a ha hv
    have h := chebyshev2.Continuum.unboundedDiagonalOperator_graph
      (fullTargetBasis a ha) (jacobi.Bessel.sigma a ha) v k
    change (fullTargetBasis a ha).repr (targetOperator a ha v) k=_ at h
    rw [hE,map_smul,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul] at h
    exact ⟨k,mul_right_cancel₀ hk h⟩
  · rintro ⟨k,rfl⟩
    refine ⟨⟨fullTargetBasis a ha k,targetOperator_basis_mem a ha k⟩,?_,targetOperator_basis a ha k⟩
    exact (norm_pos_iff.mp (by rw [(fullTargetBasis a ha).orthonormal.norm_eq_one]; norm_num))

/-- Every actual full target eigenvector at sigma_k is a scalar multiple of the original reflected transformed basis vector v_k.
Use: supplies genuine multiplicity one of the full original target eigenvalues in Proposition C.2.
Article: jacobi, Theorem 2.1.
Proof: strict monotonicity of the original sigma enumeration forces every other true graph coordinate to vanish. The complete original basis reconstructs exactly the remaining scalar multiple. -/
theorem targetOperator_eigenvector_simple (a : ℝ) (ha : -1<a) (k : ℕ)
    (v : (targetOperator a ha).domain)
    (hv : targetOperator a ha v= jacobi.Bessel.sigma a ha k • (v:Space)) :
    (v:Space)=(fullTargetBasis a ha).repr (v:Space) k • fullTargetBasis a ha k := by
  -- Simplicity follows from the original exhaustive strictly increasing sigma list, rather than a separate Sturm simplicity premise.
  classical
  apply (fullTargetBasis a ha).repr.injective
  apply lp.ext
  apply funext
  intro n
  have h := chebyshev2.Continuum.unboundedDiagonalOperator_graph
    (fullTargetBasis a ha) (jacobi.Bessel.sigma a ha) v n
  change (fullTargetBasis a ha).repr (targetOperator a ha v) n=_ at h
  rw [hv,map_smul,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul] at h
  rw [map_smul,(fullTargetBasis a ha).repr_self,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,lp.single_apply]
  by_cases hnk : n=k
  · subst n
    simp only [Pi.single_eq_same,mul_one]
  · have hdiff : jacobi.Bessel.sigma a ha k- jacobi.Bessel.sigma a ha n≠0 :=
      sub_ne_zero.mpr ((jacobi.Bessel.sigma_strictMono ha).injective.ne (Ne.symm hnk))
    have hz : (fullTargetBasis a ha).repr (v:Space) n=0 :=
      (mul_eq_zero.mp (show (jacobi.Bessel.sigma a ha k- jacobi.Bessel.sigma a ha n)*
        (fullTargetBasis a ha).repr (v:Space) n=0 by linear_combination h)).resolve_left hdiff
    simp only [Pi.single_eq_of_ne hnk,mul_zero,hz]

/-- The full original target quadratic form is strictly positive on every nonzero vector of its entire unbounded domain.
Use: completes positivity in the genuine full target spectral realization of Proposition C.2.
Article: jacobi, Theorem 2.1.
Proof: the actual Hilbert expansion of the graph pairing is a convergent sum of positive sigma_k times squared coordinates. Every summand is nonnegative and one is strictly positive for a nonzero input. -/
theorem targetOperator_strictPositive (a : ℝ) (ha : -1<a) (v : (targetOperator a ha).domain)
    (hv : (v:Space)≠0) : 0 < inner ℝ (targetOperator a ha v) (v:Space) := by
  -- The expansion converges for the full graph-domain pair, so positivity is valid beyond finite spectral combinations.
  have he (k : ℕ) : inner ℝ (targetOperator a ha v) (fullTargetBasis a ha k)*
      inner ℝ (fullTargetBasis a ha k) (v:Space)=
        jacobi.Bessel.sigma a ha k*((fullTargetBasis a ha).repr (v:Space) k)^2 := by
    have h := chebyshev2.Continuum.unboundedDiagonalOperator_graph
      (fullTargetBasis a ha) (jacobi.Bessel.sigma a ha) v k
    change (fullTargetBasis a ha).repr (targetOperator a ha v) k=_ at h
    rw [real_inner_comm (fullTargetBasis a ha k) (targetOperator a ha v),
      ← (fullTargetBasis a ha).repr_apply_apply,← (fullTargetBasis a ha).repr_apply_apply,h]
    ring
  have h := (fullTargetBasis a ha).hasSum_inner_mul_inner (targetOperator a ha v) (v:Space)
  simp only [he] at h
  obtain ⟨k,hk⟩ := target_nonzero_coordinate a ha hv
  rw [← h.tsum_eq]
  exact h.summable.tsum_pos (fun n => mul_nonneg
    (jacobi.Bessel.spectralZero_pos ha (jacobi.Bessel.sigma_mem ha n)).le (sq_nonneg _)) k
      (mul_pos (jacobi.Bessel.spectralZero_pos ha (jacobi.Bessel.sigma_mem ha k)) (sq_pos_of_ne_zero hk))

end
end jacobi.GelfandLevitan
