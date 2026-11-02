import jacobi.GelfandLevitan.HalfReflection

/-!
Article: jacobi, Proposition C.2.
The actual complete full reference system splits into two complete
orthonormal half-interval systems. The parity parameter p=0 corresponds
to the article's odd one-based indices, and p=1 to its even indices.
Use: halfReferenceVector and the transformed parity systems keep the article's one-based parity through zero-based reference indices.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set MeasureTheory Filter jacobi.Reference
open scoped Topology InnerProductSpace
set_option backward.isDefEq.respectTransparency false

/-- The unchanged original reference index in either physical parity class.
Use: halfReferenceVector and the transformed parity systems keep the article's one-based parity through zero-based reference indices.
Article: jacobi, Appendix C.2 (two transformed orthonormal bases).
-/
def parityIndex (p : Fin 2) (k : ℕ) : ℕ := 2*k+p

/-- Every original reference parity class has a constant actual reflection sign.
Use: the half-interval norm identity and completeness argument use this same original sign.
Article: jacobi, Appendix C.2 (two transformed orthonormal bases).
Proof: the original full reference parity is (-1)^(2*k+p), which is (-1)^p. -/
theorem reflectionUnitary_parity_basis (a : ℝ) (ha : -1<a) (p : Fin 2) (k : ℕ) :
    reflectionUnitary (hilbertBasis a ha (parityIndex p k))=
      (-1:ℝ)^(p:ℕ) • hilbertBasis a ha (parityIndex p k) := by
  rw [reflectionUnitary_basis,parityIndex,pow_add,pow_mul]
  norm_num

/-- Same-parity original full vectors have twice their half-projected inner product.
Use: proves the actual sqrt(2) half-reference normalization before constructing either half basis.
Article: jacobi, Appendix C.2 (two transformed orthonormal bases).
Proof: pair the actual half-projection partition with the second vector. Move its true reflection to the other slot and insert the common parity sign; the two signs multiply to one. -/
theorem halfProjection_inner_parity (v w : Space) (ε : ℝ) (hε : ε^2=1)
    (hv : reflectionUnitary v=ε • v) (hw : reflectionUnitary w=ε • w) :
    2*inner ℝ (halfSubspace.orthogonalProjectionOnto v)
      (halfSubspace.orthogonalProjectionOnto w)=inner ℝ v w := by
  -- The actual physical partition retains the original Lebesgue normalization.
  have h := congrArg (fun x:Space => inner ℝ x w) (fullHalfProjection_partition v)
  rw [inner_add_left,reflectionUnitary_inner,hv,hw,map_smul,
    real_inner_smul_left,real_inner_smul_right] at h
  have hp : inner ℝ (fullHalfProjection v) w=
      inner ℝ (halfSubspace.orthogonalProjectionOnto v) (halfSubspace.orthogonalProjectionOnto w) := by
    change inner ℝ (halfSubspace.orthogonalProjectionOnto v:Space) w=_
    exact (halfSubspace.inner_orthogonalProjectionOnto_eq_of_mem_left _ _).symm
  rw [hp,← mul_assoc,← pow_two,hε,one_mul] at h
  linarith

/-- The actual normalized reference waves restricted to the physical half interval.
Use: the two halfReferenceBasis constructions are the reference systems e_k^0 used in the GL tight-frame and compact-perturbation arguments.
Article: jacobi, Appendix C.2 (two transformed orthonormal bases).
-/
def halfReferenceVector (a : ℝ) (ha : -1<a) (p : Fin 2) (k : ℕ) : halfSubspace :=
  Real.sqrt 2 • halfSubspace.orthogonalProjectionOnto (hilbertBasis a ha (parityIndex p k))

/-- Each original parity restriction is an actual orthonormal family in the physical half-interval L2 space.
Use: completeness upgrades each family to the actual halfReferenceBasis, supplying its true Parseval identity.
Article: jacobi, Proposition C.2.
Proof: same-parity full pairings are twice their actual half pairings; the genuine sqrt(2) normalization cancels this factor. The original full system is already a complete orthonormal Hilbert basis. -/
theorem halfReferenceVector_orthonormal (a : ℝ) (ha : -1<a) (p : Fin 2) :
    Orthonormal ℝ (halfReferenceVector a ha p) := by
  -- The full system and the half projection are the actual original reference data.
  rw [orthonormal_iff_ite]
  intro i j
  have hε : ((-1:ℝ)^(p:ℕ))^2=1 := by rw [← pow_mul,Nat.mul_comm,pow_mul]; norm_num
  have h := halfProjection_inner_parity
    (hilbertBasis a ha (parityIndex p i)) (hilbertBasis a ha (parityIndex p j))
    ((-1:ℝ)^(p:ℕ)) hε (reflectionUnitary_parity_basis a ha p i)
      (reflectionUnitary_parity_basis a ha p j)
  rw [halfReferenceVector,halfReferenceVector,
    real_inner_smul_left (halfSubspace.orthogonalProjectionOnto (hilbertBasis a ha (parityIndex p i)))
      (Real.sqrt 2 • halfSubspace.orthogonalProjectionOnto (hilbertBasis a ha (parityIndex p j))) (Real.sqrt 2),
    real_inner_smul_right (halfSubspace.orthogonalProjectionOnto (hilbertBasis a ha (parityIndex p i)))
      (halfSubspace.orthogonalProjectionOnto (hilbertBasis a ha (parityIndex p j))) (Real.sqrt 2),
    ← mul_assoc,← pow_two,Real.sq_sqrt (by norm_num : (0:ℝ)≤2),h,
    (orthonormal_iff_ite.mp (hilbertBasis a ha).orthonormal) (parityIndex p i) (parityIndex p j)]
  have hi : parityIndex p i=parityIndex p j ↔ i=j := by unfold parityIndex; omega
  simp only [hi]

/-- The true parity extension of an arbitrary physical half-interval L2 input.
Use: halfReferenceVector_total proves completeness by testing this actual full-domain vector against the complete original reference basis.
Article: jacobi, Proposition C.2.
-/
def halfParityExtension (p : Fin 2) (v : halfSubspace) : Space :=
  (v:Space)+((-1:ℝ)^(p:ℕ)) • reflectionUnitary (v:Space)

/-- A half-supported input is orthogonal to the reflection of every half-supported input.
Use: restricting the genuine parity extension recovers its original half input, so completeness transfers back without losing information.
Article: jacobi, Appendix C.2 (two transformed orthonormal bases).
Proof: the reflected vector is zero on the first open half, and the original vector is zero on the second open half. The single midpoint is null. -/
theorem half_inner_reflection (v w : halfSubspace) :
    inner ℝ (v:Space) (reflectionUnitary (w:Space))=0 := by
  -- Actual L2 representatives are changed only outside their genuine null sets.
  rw [L2.inner_def]
  apply integral_eq_zero_of_ae
  filter_upwards [halfSubspace_supported v,reflectionUnitary_ae (w:Space),
    unitInterval.measurePreserving_symm.quasiMeasurePreserving.ae
      (halfSubspace_supported w),
    volume.ae_ne (⟨1/2,by norm_num⟩:Interval)] with t hv hR hw ht
  rw [hR]
  have ht' : (t:ℝ)≠1/2 := fun h => ht (Subtype.ext h)
  by_cases hp : 1/2<(t:ℝ)
  · rw [hv hp,inner_zero_left,Pi.zero_apply]
  · have hr : 1/2<(unitInterval.symm t:ℝ) := by
      rw [unitInterval.coe_symm_eq]
      have hlt := lt_of_le_of_ne (le_of_not_gt hp) ht'
      linarith
    rw [hw hr,inner_zero_right,Pi.zero_apply]

/-- A parity extension vanishes only when its genuine original half input vanishes.
Use: the complete full reference basis detects every half input orthogonal to either actual reference parity family.
Article: jacobi, Appendix C.2 (two transformed orthonormal bases).
Proof: pair the zero extension with its original half input. Disjoint reflected support removes the cross term and leaves the actual half-input norm square. -/
theorem halfParityExtension_eq_zero (p : Fin 2) (v : halfSubspace)
    (hz : halfParityExtension p v=0) : v=0 := by
  have h := congrArg (fun x:Space => inner ℝ (v:Space) x) hz
  rw [halfParityExtension,inner_add_right,real_inner_smul_right,
    half_inner_reflection,mul_zero,add_zero,inner_zero_right,inner_self_eq_zero] at h
  exact Subtype.ext h

end
end jacobi.GelfandLevitan
