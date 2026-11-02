import jacobi.GelfandLevitan.FactorizationIntegrals

/-!
Article: jacobi, Proposition C.2.
The original Volterra and source operators satisfy the printed exact
factorization. Its proof integrates the actual GL row cancellation and
then applies real polarization. Invertibility and the two bases require
the subsequent compactness and parity arguments.
Use: expresses the factorization quadratic form using the proved genuine covariance integrals.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set jacobi.Reference
open scoped Topology InnerProductSpace
attribute [local irreducible] transformationOperator kernelOperator

/-- The original identity-plus-Volterra adjoint has its actual row-integral formula.
Use: expresses the factorization quadratic form using the proved genuine covariance integrals.
Article: jacobi, Proposition C.2.
Proof: the adjoint preserves addition and fixes the identity; substitute the independently proved true Volterra adjoint integral. -/
theorem transformationPlus_adjoint (a : ℝ) (ha : -1<a) (v : halfSubspace) :
    (transformationPlus a ha).adjoint v=v+rowIntegral (volterraRows a ha) v := by
  rw [transformationPlus,map_add,add_apply,
    ContinuousLinearMap.adjoint_id,ContinuousLinearMap.id_apply,transformationOperator_adjoint]

/-- The actual GL-transformed positive form is exactly the original Hilbert norm square.
Use: real polarization proves transformation_factorization, and parity Parseval transfers this identity to the two transformed systems.
Article: jacobi, Appendix C.2 (two transformed orthonormal bases).
Proof: expand the actual form at v+K*v. The adjoint identity evaluates its two linear cross terms, source symmetry identifies its mixed covariance, and the proved integral GL cancellation eliminates the whole remaining correction. -/
theorem transformation_factorization_form (a : ℝ) (ha : -1<a) (v : halfSubspace) :
    inner ℝ (positiveOperator a ha ((transformationPlus a ha).adjoint v))
      ((transformationPlus a ha).adjoint v)=‖v‖^2 := by
  -- The correction is the actual five-integral identity, with no frame or factorization premise.
  let j := rowIntegral (volterraRows a ha) v
  have hj : j=(transformationOperator a ha).adjoint v := (transformationOperator_adjoint a ha v).symm
  have hc : inner ℝ j v=inner ℝ (transformationOperator a ha v) v := by
    rw [hj,ContinuousLinearMap.adjoint_inner_left,real_inner_comm]
  have hc' : inner ℝ v j=inner ℝ (transformationOperator a ha v) v :=
    (real_inner_comm _ _).trans hc
  have hF : inner ℝ (kernelOperator a ha j) v=inner ℝ j (kernelOperator a ha v) :=
    kernelOperator_symmetric a ha j v
  have hA : inner ℝ (positiveOperator a ha j) j=
      inner ℝ j j+inner ℝ (kernelOperator a ha j) j := by
    change inner ℝ (j+kernelOperator a ha j) j=_
    rw [inner_add_left]
  have hz := factorization_integral_zero a ha v
  change inner ℝ (kernelOperator a ha v) v+2*inner ℝ (transformationOperator a ha v) v+
    inner ℝ j (kernelOperator a ha v)+inner ℝ (kernelOperator a ha v) j+
      inner ℝ (positiveOperator a ha j) j=0 at hz
  rw [transformationPlus_adjoint]
  change inner ℝ (v+j+kernelOperator a ha (v+j)) (v+j)=_
  simp only [map_add,inner_add_left,inner_add_right,real_inner_self_eq_norm_sq,hc,hc',hF]
  rw [real_inner_self_eq_norm_sq] at hA
  linarith

/-- The original covariance conjugation is a genuinely symmetric bounded operator.
Use: its actual quadratic form determines the exact operator factorization by real polarization.
Article: jacobi, Appendix C.2 (two transformed orthonormal bases).
Proof: move each outer transformation through its true Hilbert adjoint and use the proved symmetry of the original positive source operator. -/
theorem transformation_conjugate_symmetric (a : ℝ) (ha : -1<a) :
    (transformationPlus a ha*positiveOperator a ha*(transformationPlus a ha).adjoint).IsSymmetric := by
  -- Transfer both outer transformations to the opposite slot; the remaining original source operator is symmetric.
  intro v w
  change inner ℝ (transformationPlus a ha (positiveOperator a ha ((transformationPlus a ha).adjoint v))) w=
    inner ℝ v (transformationPlus a ha (positiveOperator a ha ((transformationPlus a ha).adjoint w)))
  rw [← ContinuousLinearMap.adjoint_inner_right]
  have h := positiveOperator_symmetric a ha
    ((transformationPlus a ha).adjoint v) ((transformationPlus a ha).adjoint w)
  change inner ℝ (positiveOperator a ha ((transformationPlus a ha).adjoint v))
    ((transformationPlus a ha).adjoint w)=
      inner ℝ ((transformationPlus a ha).adjoint v)
        (positiveOperator a ha ((transformationPlus a ha).adjoint w)) at h
  rw [h,ContinuousLinearMap.adjoint_inner_left]

/-- The original GL operators satisfy the exact printed factorization, with all its hypotheses proved for their actual data.
Use: transfers each source parity spectral form to the norm square of the actual transformed family in Two orthonormal bases.
Article: jacobi, Appendix C.2 (two transformed orthonormal bases).
Source: real polarization for symmetric Hilbert operators.
Proof: the symmetric difference from the identity has identically zero quadratic form by the genuine integral factorization calculation. Community real polarization makes that actual bounded-operator difference zero. -/
theorem transformation_factorization (a : ℝ) (ha : -1<a) :
    transformationPlus a ha*positiveOperator a ha*(transformationPlus a ha).adjoint=1 := by
  -- Polarization is applied only after the actual kernel and product-integral calculations are complete.
  have hi : (ContinuousLinearMap.id ℝ halfSubspace).IsSymmetric := fun _ _ => rfl
  have hs := (transformation_conjugate_symmetric a ha).sub hi
  have hz : (transformationPlus a ha*positiveOperator a ha*(transformationPlus a ha).adjoint-1).toLinearMap=0 :=
    hs.inner_map_self_eq_zero.mp (fun v => by
      change inner ℝ (transformationPlus a ha (positiveOperator a ha ((transformationPlus a ha).adjoint v))-v) v=0
      rw [inner_sub_left,← ContinuousLinearMap.adjoint_inner_right,
        transformation_factorization_form,real_inner_self_eq_norm_sq,sub_self])
  apply sub_eq_zero.mp
  apply ContinuousLinearMap.ext
  intro v
  exact congrArg (fun T:halfSubspace →ₗ[ℝ] halfSubspace => T v) hz

/-- The original identity-plus-Volterra transformation is onto the actual half-interval Hilbert space.
Use: compact Fredholm theory upgrades this consequence of the proved factorization to genuine two-sided invertibility.
Article: jacobi, Appendix C.2 (two transformed orthonormal bases).
Proof: the original factorization explicitly supplies a preimage A*S*v of every original vector. -/
theorem transformationPlus_surjective (a : ℝ) (ha : -1<a) :
    Function.Surjective (transformationPlus a ha) := by
  intro v
  refine ⟨positiveOperator a ha ((transformationPlus a ha).adjoint v),?_⟩
  exact congrArg (fun T:halfSubspace →L[ℝ] halfSubspace => T v) (transformation_factorization a ha)

end
end jacobi.GelfandLevitan
