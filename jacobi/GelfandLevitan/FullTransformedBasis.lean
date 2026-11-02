import jacobi.GelfandLevitan.ParityExtension

/-!
Article: jacobi, Proposition C.2.
The two actual half-interval transformed bases assemble into a complete
orthonormal basis of the original full physical L2 space. Its entries
are precisely the normalized even/odd reflections of the original u_k.
This Hilbert-space assertion precedes the separate midpoint C2 matching.
Use: fullTransformedVector preserves the exact original sigma enumeration while joining the two transformed half bases.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set jacobi.Reference
open scoped Topology InnerProductSpace
set_option backward.isDefEq.respectTransparency false

/-- The original zero-based parity of a full spectral index.
Use: fullTransformedVector preserves the exact original sigma enumeration while joining the two transformed half bases.
Article: jacobi, Proposition C.2.
-/
def spectralParity (n : ℕ) : Fin 2 := ⟨n%2,Nat.mod_lt n (by norm_num)⟩

/-- The original index is recovered exactly from its physical parity class and its within-class index.
Use: fullTransformedVector_at_parity and fullTransformedVector_orthonormal keep the full target eigenvalue enumeration unchanged.
Article: jacobi, Proposition C.2.
Proof: Euclidean division by two reconstructs the unchanged natural index. -/
theorem parityIndex_spectralParity (n : ℕ) : parityIndex (spectralParity n) (n/2)=n := by
  change 2*(n/2)+n%2=n
  omega

/-- The actual full target spectral vectors, obtained by normalized physical parity reflection of the proved half-interval transformed bases.
Use: fullTargetBasis and targetOperator construct the genuine full spectral realization on the original physical L2 space.
Article: jacobi, Proposition C.2.
-/
def fullTransformedVector (a : ℝ) (ha : -1<a) (n : ℕ) : Space :=
  normalizedParityExtension (spectralParity n) (transformedParityBasis a ha (spectralParity n) (n/2))

/-- The full original family at a parity index is exactly the normalized extension of that class's actual half-basis entry.
Use: fullTransformedVector_total tests the full family against each complete transformed half basis separately.
Article: jacobi, Proposition C.2.
Proof: quotient and remainder of 2*k+p are k and p since p is a genuine residue less than two. -/
theorem fullTransformedVector_at_parity (a : ℝ) (ha : -1<a) (p : Fin 2) (k : ℕ) :
    fullTransformedVector a ha (parityIndex p k)=normalizedParityExtension p (transformedParityBasis a ha p k) := by
  have hp : spectralParity (parityIndex p k)=p := by
    apply Fin.ext
    change (2*k+(p:ℕ))%2=(p:ℕ)
    omega
  have hk : parityIndex p k/2=k := by unfold parityIndex; omega
  rw [fullTransformedVector,hp,hk]

/-- The full reflected original transformed system is orthonormal in the genuine physical full-interval L2 space.
Use: fullTargetBasis packages the actual v_k family as a community Hilbert basis before defining H_alpha.
Article: jacobi, Proposition C.2.
Proof: normalized parity extension preserves each genuine half-basis pairing and makes opposite classes orthogonal. Equal parity and equal within-class index reconstruct equal original indices. -/
theorem fullTransformedVector_orthonormal (a : ℝ) (ha : -1<a) :
    Orthonormal ℝ (fullTransformedVector a ha) := by
  -- The full Lebesgue normalization is supplied by the proved sqrt(2) extension identity.
  classical
  rw [orthonormal_iff_ite]
  intro i j
  rw [fullTransformedVector,fullTransformedVector,normalizedParityExtension_inner]
  by_cases hp : spectralParity i=spectralParity j
  · rw [ite_eq_left hp,hp,(orthonormal_iff_ite.mp (transformedParityBasis a ha (spectralParity j)).orthonormal)]
    have he : i/2=j/2 ↔ i=j := by
      constructor
      · intro h
        have hi := parityIndex_spectralParity i
        have hj := parityIndex_spectralParity j
        rw [hp,h] at hi
        exact hi.symm.trans hj
      · exact congrArg (fun n => n/2)
    simp only [he]
  · have hij : i≠j := fun h => hp (congrArg spectralParity h)
    rw [ite_eq_right hp,ite_eq_right hij]

/-- Orthogonality to every actual full reflected target wave forces the original full L2 input to vanish.
Use: fullTargetBasis obtains genuine completeness of the same v_k family, without a full-basis premise.
Article: jacobi, Proposition C.2.
Proof: the full coefficients are exactly the half coefficients of each restricted parity part. Completeness of each actual transformed half basis makes both parts zero, and the genuine physical projection partition recovers the full input. -/
theorem fullTransformedVector_total (a : ℝ) (ha : -1<a) (v : Space)
    (hv : ∀ n,inner ℝ (fullTransformedVector a ha n) v=0) : v=0 := by
  -- Both completeness inputs were proved for the actual u functions before the full family was defined.
  have hparts (p : Fin 2) : parityRestriction p v=0 := by
    apply (transformedParityBasis a ha p).repr.injective
    apply lp.ext
    apply funext
    intro k
    have h := hv (parityIndex p k)
    rw [fullTransformedVector_at_parity,normalizedParityExtension_pairing] at h
    have hi := (mul_eq_zero.mp h).resolve_left
      (inv_ne_zero (Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<2)).ne')
    rw [(transformedParityBasis a ha p).repr_apply_apply,hi,map_zero]
    rfl
  exact parityRestriction_total v (hparts 0) (hparts 1)

/-- The original full reflected transformed family has zero orthogonal complement.
Use: fullTargetBasis applies the community complete-orthonormal-family constructor to the actual original functions.
Article: jacobi, Theorem 2.1.
Proof: orthogonality to the actual span gives each original zero coefficient, so fullTransformedVector_total applies. -/
theorem fullTransformedVector_orthogonal_eq_bot (a : ℝ) (ha : -1<a) :
    (Submodule.span ℝ (range (fullTransformedVector a ha)))ᗮ=⊥ := by
  apply le_antisymm ?_ bot_le
  intro v hv
  exact fullTransformedVector_total a ha v (fun k =>
    (Submodule.mem_orthogonal _ _).mp hv _ (Submodule.subset_span (mem_range_self k)))

/-- The actual complete Hilbert basis of full original reflected transformed waves.
Use: targetOperator and targetGreenOperator use this same physical basis for the full original sigma spectrum.
Article: jacobi, Proposition C.2.
-/
def fullTargetBasis (a : ℝ) (ha : -1<a) : HilbertBasis ℕ ℝ Space :=
  HilbertBasis.mkOfOrthogonalEqBot (fullTransformedVector_orthonormal a ha)
    (fullTransformedVector_orthogonal_eq_bot a ha)

/-- Each entry of the genuine full target Hilbert basis is the actual reflected transformed function defined before packaging the basis.
Use: all full spectral operator assertions retain the original u_k functions and physical reflection, rather than an abstract orthonormal replacement.
Article: jacobi, Proposition C.2.
Proof: the community complete-orthonormal-family constructor preserves its actual input family. -/
theorem fullTargetBasis_apply (a : ℝ) (ha : -1<a) (k : ℕ) :
    fullTargetBasis a ha k=fullTransformedVector a ha k :=
  congrFun (HilbertBasis.coe_mkOfOrthogonalEqBot _ _) k

/-- Every original full target basis vector has its exact physical midpoint reflection sign.
Use: targetOperator_reflection establishes actual reflection invariance of the full spectral realization.
Article: jacobi, Proposition C.2.
Proof: the actual normalized parity extension has precisely its proved parity sign. Euclidean parity is the original index modulo two. -/
theorem fullTargetBasis_reflection (a : ℝ) (ha : -1<a) (k : ℕ) :
    reflectionUnitary (fullTargetBasis a ha k)=(-1:ℝ)^k • fullTargetBasis a ha k := by
  rw [fullTargetBasis_apply,fullTransformedVector,normalizedParityExtension_reflection]
  have he : (-1:ℝ)^(spectralParity k:ℕ)=(-1:ℝ)^k := by
    change (-1:ℝ)^(k%2)=(-1:ℝ)^k
    rw [← parityIndex_spectralParity k,parityIndex,pow_add,pow_mul]
    norm_num [spectralParity]
  rw [he]

end
end jacobi.GelfandLevitan
