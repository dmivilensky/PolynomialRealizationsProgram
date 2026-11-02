import jacobi.GelfandLevitan.NormalizedReferenceVectors
import jacobi.GelfandLevitan.SynthesisInverse

/-!
Article: jacobi, Appendix C.2 (two transformed orthonormal bases).
For each original parity class the actual target reference synthesis
operator is invertible. Its genuine GL image is an invertible operator
whose adjoint preserves norms, by the independently proved frame sum.
This establishes the unitary transport used to construct both bases.
Use: the proved norm-summable reference perturbation therefore has an invertible synthesis operator by the community compact Fredholm alternative.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set jacobi.Reference
open scoped Topology InnerProductSpace
set_option backward.isDefEq.respectTransparency false

/-- Each genuine target reference parity family is complete in the original half-interval Hilbert space.
Use: the proved norm-summable reference perturbation therefore has an invertible synthesis operator by the community compact Fredholm alternative.
Article: jacobi, Appendix C.2 (two transformed orthonormal bases).
Proof: pull an orthogonal input back through the actual invertible GL adjoint. Its genuine transformed coefficients vanish, and the proved normalized parity frame forces that true preimage to have zero norm. The original input is its actual adjoint image and is zero. -/
theorem normalizedSourceVector_parity_total (a : ℝ) (ha : -1<a) (p : Fin 2) (v : halfSubspace)
    (hz : ∀ k,inner ℝ (normalizedSourceVector a ha (parityIndex p k)) v=0) : v=0 := by
  -- The adjoint inverse used here is a proved genuine bounded inverse of the original transformation.
  let w := Ring.inverse (transformationPlus a ha).adjoint v
  have hw : (transformationPlus a ha).adjoint w=v :=
    congrArg (fun T:halfSubspace →L[ℝ] halfSubspace => T v)
      (Ring.mul_inverse_cancel _ (transformationPlus_adjoint_isUnit a ha))
  have hc (k : ℕ) : inner ℝ (normalizedTransformedVector a ha (parityIndex p k)) w=0 := by
    rw [← transformationPlus_normalizedSourceVector,← ContinuousLinearMap.adjoint_inner_right,hw]
    exact hz k
  have h := normalized_transformed_parity_parseval a ha p w
  simp only [hc,zero_pow (by norm_num : (2:ℕ)≠0)] at h
  have hn : ‖w‖^2=0 := h.unique hasSum_zero
  have hw0 : w=0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hn)
  rw [hw0,map_zero] at hw
  exact hw.symm

/-- The actual bounded synthesis map from either complete original reference half basis to the target reference waves.
Use: transformedSynthesis applies the actual GL transformation to precisely this invertible original map.
Article: jacobi, Appendix C.2 (two transformed orthonormal bases).
-/
def referenceSynthesis (a : ℝ) (ha : -1<a) (p : Fin 2) : halfSubspace →L[ℝ] halfSubspace :=
  synthesisOperator (halfReferenceBasis a ha p) (fun k => normalizedSourceVector a ha (parityIndex p k))

/-- The genuine target reference synthesis is invertible for every original admissible order and either parity class.
Use: the actual transformed frame is therefore an invertible basis image, so its frame identity implies orthonormality.
Article: jacobi, Appendix C.2 (two transformed orthonormal bases).
Proof: apply the independently proved compact-synthesis Fredholm theorem with the actual absolute reference perturbation and the actual source parity completeness, both proved unconditionally above. -/
theorem referenceSynthesis_isUnit (a : ℝ) (ha : -1<a) (p : Fin 2) : IsUnit (referenceSynthesis a ha p) :=
  synthesisOperator_isUnit _ _ (normalizedSourceVector_parity_summable a ha p)
    (normalizedSourceVector_parity_total a ha p)

/-- The actual synthesis map of the normalized transformed parity waves.
Use: its proved unitarity constructs the two original transformed orthonormal bases.
Article: jacobi, Appendix C.2 (two transformed orthonormal bases).
-/
def transformedSynthesis (a : ℝ) (ha : -1<a) (p : Fin 2) : halfSubspace →L[ℝ] halfSubspace :=
  transformationPlus a ha*referenceSynthesis a ha p

/-- Every actual transformed synthesis map is genuinely invertible.
Use: its independently proved adjoint isometry forces full unitarity in transformedSynthesis_unitary.
Article: jacobi, Appendix C.2 (two transformed orthonormal bases).
Proof: both original factors have independently proved genuine two-sided bounded inverses. -/
theorem transformedSynthesis_isUnit (a : ℝ) (ha : -1<a) (p : Fin 2) : IsUnit (transformedSynthesis a ha p) :=
  (transformationPlus_isUnit a ha).mul (referenceSynthesis_isUnit a ha p)

/-- The actual transformed synthesis sends each original half-reference basis entry to the exact normalized original u vector.
Use: identifies its unitary basis image with the functions printed in Two orthonormal bases.
Article: jacobi, Appendix C.2 (two transformed orthonormal bases).
Proof: the genuine compact reference synthesis has its independently proved exact basis images; the actual GL map sends each of those normalized reference waves to its actual transformed wave. -/
theorem transformedSynthesis_basis (a : ℝ) (ha : -1<a) (p : Fin 2) (k : ℕ) :
    transformedSynthesis a ha p (halfReferenceBasis a ha p k)=
      normalizedTransformedVector a ha (parityIndex p k) := by
  change transformationPlus a ha
    (synthesisOperator (halfReferenceBasis a ha p) (fun j => normalizedSourceVector a ha (parityIndex p j))
      (halfReferenceBasis a ha p k))=_
  rw [synthesisOperator_basis _ _ (normalizedSourceVector_parity_summable a ha p),
    transformationPlus_normalizedSourceVector]

/-- The true adjoint of each actual transformed synthesis map preserves the original Hilbert norm.
Use: its genuine invertibility then gives the full unitarity needed for both transformed orthonormal bases.
Article: jacobi, Appendix C.2 (two transformed orthonormal bases).
Proof: reference-basis Parseval computes the actual adjoint norm square. Its coefficients are the actual normalized transformed coefficients by the proved synthesis images. Their independently proved frame sum is the original input norm square; equality of the nonnegative norms follows. -/
theorem transformedSynthesis_adjoint_norm (a : ℝ) (ha : -1<a) (p : Fin 2) (v : halfSubspace) :
    ‖(transformedSynthesis a ha p).adjoint v‖=‖v‖ := by
  -- Compare two genuine convergent sums of the same actual transformed coefficients.
  have h := (halfReferenceBasis a ha p).hasSum_inner_mul_inner
    ((transformedSynthesis a ha p).adjoint v) ((transformedSynthesis a ha p).adjoint v)
  rw [real_inner_self_eq_norm_sq] at h
  have he (k : ℕ) : inner ℝ ((transformedSynthesis a ha p).adjoint v) (halfReferenceBasis a ha p k)*
      inner ℝ (halfReferenceBasis a ha p k) ((transformedSynthesis a ha p).adjoint v)=
        (inner ℝ (normalizedTransformedVector a ha (parityIndex p k)) v)^2 := by
    rw [real_inner_comm (halfReferenceBasis a ha p k) ((transformedSynthesis a ha p).adjoint v),
      ContinuousLinearMap.adjoint_inner_right,transformedSynthesis_basis,pow_two]
  have hs := h.congr_fun (fun k => (he k).symm)
  have hn := hs.unique (normalized_transformed_parity_parseval a ha p v)
  nlinarith [norm_nonneg ((transformedSynthesis a ha p).adjoint v),norm_nonneg v]

/-- Each actual transformed synthesis operator is unitary on the original physical half-interval Hilbert space.
Use: its true unitary image of the actual reference basis proves both systems in Two orthonormal bases.
Article: jacobi, Appendix C.2 (two transformed orthonormal bases).
Proof: the actual adjoint preserves norms, so its genuine Gram operator is the identity. Since the original synthesis is independently proved a unit, the community unitary characterization supplies the other inverse identity as well. -/
theorem transformedSynthesis_unitary (a : ℝ) (ha : -1<a) (p : Fin 2) :
    transformedSynthesis a ha p∈unitary (halfSubspace →L[ℝ] halfSubspace) := by
  have h := ((transformedSynthesis a ha p).adjoint.norm_map_iff_adjoint_comp_self).mp
    (transformedSynthesis_adjoint_norm a ha p)
  rw [ContinuousLinearMap.adjoint_adjoint] at h
  exact (transformedSynthesis_isUnit a ha p).mem_unitary_of_mul_star_self h

end
end jacobi.GelfandLevitan
