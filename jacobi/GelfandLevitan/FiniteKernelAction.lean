import jacobi.GelfandLevitan.FiniteKernelMaps
import jacobi.GelfandLevitan.FiniteCompression
import jacobi.GelfandLevitan.KernelRepresentative

/-!
Article: jacobi, Proposition C.2.
The finite spectral operators act through precisely their original
finite continuous kernels. Exact feature expansions identify the actual
Hilbert operator with its continuous integral representative, before
the finite inverse reconstruction is used as a GL solution.
Use: finiteKernelActionMap is the literal original finite F^(N) integral, and its genuine projected representative gives the finite GL spatial equation.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set Filter MeasureTheory jacobi.Reference
open scoped Topology InnerProductSpace
attribute [local instance] Measure.Subtype.measureSpace
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] kernelTerm realSolution rankCorrection

/-- The actual continuous-row embedding pairs with an original half-supported Hilbert input by the genuine spatial integral.
Use: finiteKernelActionMap is the literal original finite F^(N) integral, and its genuine projected representative gives the finite GL spatial equation.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: the true orthogonal projection preserves the original Hilbert pairing, and the continuous-to-L2 embedding has its genuine original almost-everywhere representative. -/
theorem rowEmbedding_inner (g : C(Interval,ℝ)) (v : halfSubspace) :
    inner ℝ (rowEmbedding g) v=∫ r : Interval,(v:Space) r*g r := by
  change inner ℝ (halfSubspace.orthogonalProjectionOnto (ContinuousMap.toLp (𝕜 := ℝ) (p := 2) volume g)) v=_
  rw [halfSubspace.inner_orthogonalProjectionOnto_eq_of_mem_right,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [ContinuousMap.coeFn_toLp (𝕜 := ℝ) (p := 2) volume g] with r hr
  rw [hr]
  rfl

/-- Each genuine original finite kernel row has its exact original two-feature continuous-function expansion.
Use: finiteKernelRowVector_expansion and finiteKernelAction_eq identify the actual finite inverse operator with the same finite source kernel.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: evaluate the genuine continuous row, preserve the original physical half coordinate and expand the original kernelTerm formula. -/
theorem kernelTermMap_row (a : ℝ) (ha : -1<a) (k : ℕ) (t : HalfInterval) :
    (kernelTermMap a ha k).curry (halfInclusion t)=
      (normingRatio a ha k/norming a k*realSolution a (jacobi.Bessel.sigma a ha k) t) • realHalfWave a ha (jacobi.Bessel.sigma a ha k)-
      (1/norming a k*realSolution a (eigenvalue a k) t) • realHalfWave a ha (eigenvalue a k) := by
  ext r
  change kernelTerm a ha k (min (t:ℝ) (1/2)) (halfTime r)=_
  rw [min_eq_left t.property.2,kernelTerm]
  change _=(_*realSolution a (jacobi.Bessel.sigma a ha k) (halfTime r)-_*realSolution a (eigenvalue a k) (halfTime r))
  ring

/-- Every actual finite source Hilbert row is exactly the sum of its original norming-weighted genuine source feature vectors.
Use: proves finiteKernelAction_eq without assuming an integral representation of the finite spectral operator.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: the finite continuous row is its original finite sum; apply the same original row embedding to each genuine two-feature row and use linearity. -/
theorem finiteKernelRowVector_expansion (a : ℝ) (ha : -1<a) (N : ℕ) (t : HalfInterval) :
    finiteKernelRowVector a ha N t=∑ k∈Finset.range N,(
      (normingRatio a ha k/norming a k*realSolution a (jacobi.Bessel.sigma a ha k) t) • coefficientVector a ha (jacobi.Bessel.sigma a ha k)-
      (1/norming a k*realSolution a (eigenvalue a k) t) • coefficientVector a ha (eigenvalue a k)) := by
  -- The finite expansion is established in the actual continuous function space before its original Hilbert inclusion.
  have he : finiteKernelRows a ha N t=∑ k∈Finset.range N,(kernelTermMap a ha k).curry (halfInclusion t) := by
    ext r
    simp only [finiteKernelRows,ContinuousMap.comp_apply,ContinuousMap.curry_apply,finiteKernelMap,ContinuousMap.sum_apply]
  change rowEmbedding (finiteKernelRows a ha N t)=_
  rw [he,map_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [kernelTermMap_row,map_sub,map_smul,map_smul]
  rfl

/-- The genuine continuous action of the literal finite spectral GL kernel on an original Hilbert input.
Use: finiteKernelAction_eq identifies its projected actual L2 image with the original finite rankCorrection sum, giving the exact finite spatial GL equation.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
-/
def finiteKernelActionMap (a : ℝ) (ha : -1<a) (N : ℕ) (v : halfSubspace) : C(Interval,ℝ) :=
  ⟨fun s => inner ℝ (finiteKernelRowVector a ha N (halfClamp s)) v,
    ((finiteKernelRowVector a ha N).continuous.comp halfClamp.continuous).inner continuous_const⟩

/-- The actual finite continuous kernel action is the original finite spectral operator after its genuine half-Hilbert-space embedding.
Use: finiteKernelOperator_ae supplies the correct original physical representative in the finite inverse GL equation; no kernel-action premise is assumed.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: expand the original finite source row and its genuine coefficient pairings. Its continuous action is the same finite weighted feature sum. The true row embedding maps each original feature to its original coefficient vector, giving exactly the original finite rank-one corrections. -/
theorem finiteKernelAction_eq (a : ℝ) (ha : -1<a) (N : ℕ) (v : halfSubspace) :
    rowEmbedding (finiteKernelActionMap a ha N v)=finiteKernelOperator a ha N v := by
  -- Identify the genuine continuous representative before projecting it into the original quotient Hilbert space.
  have he : finiteKernelActionMap a ha N v=∑ k∈Finset.range N,(
      (normingRatio a ha k/norming a k*realCoefficient a (v:Space) (jacobi.Bessel.sigma a ha k)) • realHalfWave a ha (jacobi.Bessel.sigma a ha k)-
      (1/norming a k*realCoefficient a (v:Space) (eigenvalue a k)) • realHalfWave a ha (eigenvalue a k)) := by
    ext s
    change inner ℝ (finiteKernelRowVector a ha N (halfClamp s)) v=_
    rw [finiteKernelRowVector_expansion,sum_inner]
    simp only [ContinuousMap.sum_apply]
    apply Finset.sum_congr rfl
    intro k _
    rw [inner_sub_left,
      real_inner_smul_left (coefficientVector a ha (jacobi.Bessel.sigma a ha k)) v
        (normingRatio a ha k/norming a k*realSolution a (jacobi.Bessel.sigma a ha k) (halfClamp s)),
      real_inner_smul_left (coefficientVector a ha (eigenvalue a k)) v
        (1/norming a k*realSolution a (eigenvalue a k) (halfClamp s)),
      coefficientVector_inner,coefficientVector_inner]
    change _=(_*realSolution a (jacobi.Bessel.sigma a ha k) (halfTime s)-_*realSolution a (eigenvalue a k) (halfTime s))
    change (_*realSolution a (jacobi.Bessel.sigma a ha k) (halfTime s))*_-(_*realSolution a (eigenvalue a k) (halfTime s))*_=_
    ring
  rw [he,map_sum]
  change _=(∑ k∈Finset.range N,rankCorrection a ha k) v
  rw [sum_apply]
  apply Finset.sum_congr rfl
  intro k _
  rw [map_sub,map_smul,map_smul,rankCorrection]
  simp only [sub_apply,smul_apply,InnerProductSpace.rankOne_apply,coefficientVector_inner,smul_smul]
  rfl

/-- The actual finite spectral GL operator has its exact original continuous-kernel representative on the physical half interval and its genuine zero extension outside.
Use: the finite inverse row equation becomes the literal original finite GL integral equation almost everywhere on its physical prefix.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: identify the actual finite spectral operator with its independently derived continuous source action, then use the already proved original half-projection representative. -/
theorem finiteKernelOperator_ae (a : ℝ) (ha : -1<a) (N : ℕ) (v : halfSubspace) :
    (finiteKernelOperator a ha N v:Space)=ᵐ[volume]
      (prefixSet (1/2)).indicator (finiteKernelActionMap a ha N v) := by
  rw [← finiteKernelAction_eq]
  exact halfProjection_toLp_ae (finiteKernelActionMap a ha N v)

end
end jacobi.GelfandLevitan
