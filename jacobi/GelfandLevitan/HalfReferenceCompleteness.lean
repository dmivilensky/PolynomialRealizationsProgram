import jacobi.GelfandLevitan.HalfReferenceBasis

/-!
Article: jacobi, Appendix C.2 (two transformed orthonormal bases).
Both actual half-reference families are complete. Their genuine
parity extensions are tested against the already complete full
reference basis; the opposite parity coefficients cancel exactly.
Use: constructs the two actual complete halfReferenceBasis systems, whose Parseval identities feed the transformed tight-frame calculation.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set jacobi.Reference
open scoped Topology InnerProductSpace
set_option backward.isDefEq.respectTransparency false

/-- Either original half-reference parity family detects every physical half-interval L2 vector.
Use: constructs the two actual complete halfReferenceBasis systems, whose Parseval identities feed the transformed tight-frame calculation.
Article: jacobi, Appendix C.2 (two transformed orthonormal bases).
Proof: extend the input with the genuine original parity sign. Same-parity full coefficients vanish by the half orthogonality assumption; opposite-parity coefficients cancel under the proved physical reflection. The complete full reference basis forces this actual extension to be zero, and its proved injectivity recovers the half input. -/
theorem halfReferenceVector_total (a : ℝ) (ha : -1<a) (p : Fin 2) (v : halfSubspace)
    (hz : ∀ k,inner ℝ (halfReferenceVector a ha p k) v=0) : v=0 := by
  -- Both parity classes use the same original full basis; no half-domain completeness premise is added.
  have hsame (k : ℕ) : inner ℝ (hilbertBasis a ha (parityIndex p k)) (v:Space)=0 := by
    have h := hz k
    rw [halfReferenceVector,real_inner_smul_left
      (halfSubspace.orthogonalProjectionOnto (hilbertBasis a ha (parityIndex p k))) v (Real.sqrt 2),
      halfSubspace.inner_orthogonalProjectionOnto_eq_of_mem_right] at h
    exact (mul_eq_zero.mp h).resolve_left (Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<2)).ne'
  have hfull (n : ℕ) : inner ℝ (hilbertBasis a ha n) (halfParityExtension p v)=0 := by
    rw [halfParityExtension,inner_add_right,
      real_inner_smul_right (hilbertBasis a ha n) (reflectionUnitary (v:Space)) ((-1:ℝ)^(p:ℕ)),
      ← reflectionUnitary_inner,reflectionUnitary_basis,
      real_inner_smul_left (hilbertBasis a ha n) (v:Space) ((-1:ℝ)^n)]
    by_cases hp : n%2=(p:ℕ)
    · have he : parityIndex p (n/2)=n := by unfold parityIndex; omega
      rw [← he,hsame,mul_zero,mul_zero,add_zero]
    · have hsign : 1+(-1:ℝ)^(p:ℕ)*(-1:ℝ)^n=0 := by
        obtain ⟨k,hk|hk⟩ := Nat.even_or_odd' n <;> subst n <;> fin_cases p <;>
          simp_all [pow_add,pow_mul]
      calc
        _ = (1+(-1:ℝ)^(p:ℕ)*(-1:ℝ)^n)*inner ℝ (hilbertBasis a ha n) (v:Space) := by ring
        _ = 0 := by rw [hsign,zero_mul]
  apply halfParityExtension_eq_zero p v
  apply (hilbertBasis a ha).repr.injective
  apply lp.ext
  apply funext
  intro n
  rw [(hilbertBasis a ha).repr_apply_apply,hfull,map_zero]
  rfl

/-- The orthogonal complement of either actual half-reference span is zero.
Use: the community HilbertBasis constructor packages each proved original complete orthonormal family.
Article: jacobi, Appendix C.2 (two transformed orthonormal bases).
Proof: any vector orthogonal to the actual span is orthogonal to every actual basis candidate, hence zero by halfReferenceVector_total. -/
theorem halfReferenceVector_orthogonal_eq_bot (a : ℝ) (ha : -1<a) (p : Fin 2) :
    (Submodule.span ℝ (range (halfReferenceVector a ha p)))ᗮ=⊥ := by
  apply le_antisymm ?_ bot_le
  intro v hv
  exact halfReferenceVector_total a ha p v (fun k =>
    (Submodule.mem_orthogonal _ _).mp hv _ (Submodule.subset_span (mem_range_self k)))

/-- The two genuine complete orthonormal half-interval reference bases.
Use: their true Parseval identities and compactly perturbed target families yield the two transformed bases of Proposition C.2.
Article: jacobi, Appendix C.2 (two transformed orthonormal bases).
-/
def halfReferenceBasis (a : ℝ) (ha : -1<a) (p : Fin 2) : HilbertBasis ℕ ℝ halfSubspace :=
  HilbertBasis.mkOfOrthogonalEqBot (halfReferenceVector_orthonormal a ha p)
    (halfReferenceVector_orthogonal_eq_bot a ha p)

/-- Every entry of the two genuine half-reference bases is exactly its actual normalized physical reference vector.
Use: identifies community Parseval coefficients with the original source coefficient integrals in the two-bases argument.
Article: jacobi, Appendix C.2 (two transformed orthonormal bases).
Proof: the community HilbertBasis constructor retains the proved original family. -/
theorem halfReferenceBasis_apply (a : ℝ) (ha : -1<a) (p : Fin 2) (k : ℕ) :
    halfReferenceBasis a ha p k=halfReferenceVector a ha p k :=
  congrFun (HilbertBasis.coe_mkOfOrthogonalEqBot _ _) k

end
end jacobi.GelfandLevitan
