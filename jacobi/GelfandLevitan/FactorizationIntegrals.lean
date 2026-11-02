import jacobi.GelfandLevitan.RowIntegrals
import jacobi.GelfandLevitan.TriangularIntegrals

/-!
Article: jacobi, Proposition C.2.
The original source operator is also the Bochner integral of its
continuous Hilbert rows. The five actual covariance terms are true
integrable scalar functions; their sum is the vanishing kernel already
obtained from the original compressed GL equation.
Use: rowIntegral_source identifies their genuine integral with the original F operator in the factorization.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set MeasureTheory Filter jacobi.Reference
open scoped Topology InnerProductSpace
attribute [local instance] Measure.Subtype.measureSpace
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] transformationKernel kernel solutionRow

/-- The actual continuous source rows on the common physical domain.
Use: rowIntegral_source identifies their genuine integral with the original F operator in the factorization.
Article: jacobi, Proposition C.2.
-/
def sourceRows (a : ℝ) (ha : -1<a) : C(Interval,halfSubspace) :=
  (kernelRowVector a ha).comp halfClamp

/-- The actual source operator's pairing is its single original row-pairing integral.
Use: identifies its Hilbert-valued row-integral representation without postulating an adjoint kernel.
Article: jacobi, Proposition C.2.
Proof: use the proved equality with the actual integral operator, preserve the pairing through the half-domain projection and substitute its continuous L2 representative almost everywhere. -/
theorem kernelOperator_inner_single (a : ℝ) (ha : -1<a) (v w : halfSubspace) :
    inner ℝ (kernelOperator a ha v) w=
      ∫ t:Interval,(w:Space) t*inner ℝ (kernelRowVector a ha (halfClamp t)) v := by
  rw [← integralKernelOperator_eq]
  change inner ℝ (halfSubspace.orthogonalProjectionOnto
    (ContinuousMap.toLp (𝕜 := ℝ) (p := 2) volume (kernelActionMap a ha v))) w=_
  rw [halfSubspace.inner_orthogonalProjectionOnto_eq_of_mem_right,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [ContinuousMap.coeFn_toLp (𝕜 := ℝ) (p := 2) volume (kernelActionMap a ha v)] with t ht
  rw [ht]
  rfl

/-- The actual original source operator is the true Bochner integral of its Hilbert rows.
Use: evaluates all mixed source/transformation covariance terms in the operator factorization.
Article: jacobi, Proposition C.2.
Proof: test the actual row integral against an arbitrary Hilbert vector. Its proved scalar integral is the source operator pairing; actual source symmetry gives the required variable order. -/
theorem rowIntegral_source (a : ℝ) (ha : -1<a) (v : halfSubspace) :
    rowIntegral (sourceRows a ha) v=kernelOperator a ha v := by
  apply ext_inner_right ℝ
  intro w
  rw [rowIntegral_inner]
  change (∫ t:Interval,(v:Space) t*inner ℝ (kernelRowVector a ha (halfClamp t)) w)=_
  rw [← kernelOperator_inner_single]
  exact (real_inner_comm _ _).trans ((kernelOperator_symmetric a ha) v w).symm

/-- The continuous symmetric triangular transformation kernel on the original product domain.
Use: its supremum norm supplies true integrability of the K+K* term in the factorization covariance.
Article: jacobi, Proposition C.2.
-/
def symmetricTransformationKernelMap (a : ℝ) (ha : -1<a) : C(Interval×Interval,ℝ) :=
  ⟨fun p => symmetricTransformationKernel a ha (halfClamp p.1) (halfClamp p.2),
    (transformationKernel_continuous a ha).comp
      (((halfClamp.continuous.comp continuous_fst).max (halfClamp.continuous.comp continuous_snd)).prodMk
        ((halfClamp.continuous.comp continuous_fst).min (halfClamp.continuous.comp continuous_snd)))⟩

/-- The symmetric transformation bilinear integral is genuinely integrable.
Use: permits adding it to the independently integrable covariance terms before applying the pointwise GL cancellation.
Article: jacobi, Proposition C.2.
Proof: use the independent-variable L1 product and the actual bounded continuous symmetric transformation kernel. -/
theorem symmetricTransformation_integrable (a : ℝ) (ha : -1<a) (v w : halfSubspace) :
    Integrable (fun p:Interval×Interval => ((v:Space) p.1*(w:Space) p.2)*
      symmetricTransformationKernel a ha (halfClamp p.1) (halfClamp p.2))
      (volume.prod volume) :=
  ((space_integrable (v:Space)).mul_prod (space_integrable (w:Space))).mul_bdd
    (symmetricTransformationKernelMap a ha).continuous.aestronglyMeasurable
    (Eventually.of_forall (symmetricTransformationKernelMap a ha).norm_coe_le_norm)

/-- The actual five covariance integrals cancel exactly.
Use: this is the scalar integral identity for the quadratic form of (I+K)(I+F)(I+K)*-I.
Article: jacobi, Proposition C.2.
Proof: every separate integral is proved integrable on the original product measure. Combine them, distribute the common original input product, and apply the actual pointwise GL covariance cancellation. -/
theorem factorization_integral_zero (a : ℝ) (ha : -1<a) (v : halfSubspace) :
    inner ℝ (kernelOperator a ha v) v+
      2*inner ℝ (transformationOperator a ha v) v+
      inner ℝ (rowIntegral (volterraRows a ha) v) (kernelOperator a ha v)+
      inner ℝ (kernelOperator a ha v) (rowIntegral (volterraRows a ha) v)+
      inner ℝ (positiveOperator a ha (rowIntegral (volterraRows a ha) v))
        (rowIntegral (volterraRows a ha) v)=0 := by
  -- Integrating the actual residual retains the genuine source and transformation rows throughout.
  have hIKF := rowIntegral_inner_twice (volterraRows a ha) (sourceRows a ha)
    (ContinuousLinearMap.id ℝ halfSubspace) v v
  have hIFK := rowIntegral_inner_twice (sourceRows a ha) (volterraRows a ha)
    (ContinuousLinearMap.id ℝ halfSubspace) v v
  dsimp only [ContinuousLinearMap.id_apply] at hIKF hIFK
  rw [kernelOperator_quadratic,transformationOperator_quadratic_twice,
    ← rowIntegral_source a ha v,hIKF,hIFK,rowIntegral_inner_twice]
  unfold kernelQuadratic
  have hF := kernelBilinear_integrable a ha (v:Space) (v:Space)
  have hK := symmetricTransformation_integrable a ha v v
  have hKF := rowCovariance_integrable (volterraRows a ha) (sourceRows a ha)
    (ContinuousLinearMap.id ℝ halfSubspace) v v
  have hFK := rowCovariance_integrable (sourceRows a ha) (volterraRows a ha)
    (ContinuousLinearMap.id ℝ halfSubspace) v v
  have hA := rowCovariance_integrable (volterraRows a ha) (volterraRows a ha)
    (positiveOperator a ha) v v
  dsimp only [ContinuousLinearMap.id_apply] at hKF hFK
  have h1 := integral_add (hF.add hK) hKF
  have h2 := integral_add ((hF.add hK).add hKF) hFK
  have h3 := integral_add (((hF.add hK).add hKF).add hFK) hA
  dsimp only [Pi.add_apply] at h1 h2 h3
  rw [← integral_add hF hK,← h1,← h2,← h3]
  apply integral_eq_zero_of_ae
  exact Eventually.of_forall (fun p => by
    change ((v:Space) p.1*(v:Space) p.2)*kernel a ha (halfTime p.1) (halfTime p.2)+
      ((v:Space) p.1*(v:Space) p.2)*symmetricTransformationKernel a ha (halfClamp p.1) (halfClamp p.2)+
      ((v:Space) p.1*(v:Space) p.2)*inner ℝ (solutionRow a ha (halfClamp p.1)) (kernelRowVector a ha (halfClamp p.2))+
      ((v:Space) p.1*(v:Space) p.2)*inner ℝ (kernelRowVector a ha (halfClamp p.1)) (solutionRow a ha (halfClamp p.2))+
      ((v:Space) p.1*(v:Space) p.2)*inner ℝ (positiveOperator a ha (solutionRow a ha (halfClamp p.1)))
        (solutionRow a ha (halfClamp p.2))=0
    rw [← mul_add,← mul_add,← mul_add,← mul_add]
    change ((v:Space) p.1*(v:Space) p.2)*factorizationKernel a ha (halfClamp p.1) (halfClamp p.2)=0
    rw [factorizationKernel_zero,mul_zero])

end
end jacobi.GelfandLevitan
