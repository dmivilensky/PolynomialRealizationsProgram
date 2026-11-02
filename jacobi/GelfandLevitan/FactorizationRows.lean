import jacobi.GelfandLevitan.IntegralEquation

/-!
Article: jacobi, Proposition C.2.
The compressed GL equation annihilates its residual against every
earlier solution row. This proves the pointwise symmetric kernel
cancellation underlying (I+K)(I+F)(I+K)*=I, before integration.
Use: tests the later compressed GL equation against an earlier row in factorizationRows_zero.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set MeasureTheory Filter jacobi.Reference
open scoped Topology InnerProductSpace

/-- An earlier GL row lies in every later physical prefix subspace.
Use: tests the later compressed GL equation against an earlier row in factorizationRows_zero.
Article: jacobi, Proposition C.2.
Proof: the actual earlier row vanishes beyond its endpoint, hence also beyond any larger endpoint. -/
theorem solutionRow_mem_later (a : ℝ) (ha : -1<a) (t s : HalfInterval)
    (hst : (s:ℝ)≤(t:ℝ)) : solutionRow a ha s∈cutoffSubspace (t:ℝ) := by
  apply (mem_cutoffSubspace_iff _ _).mpr
  filter_upwards [(mem_cutoffSubspace_iff _ _).mp (solutionRow_mem a ha s)] with r hr
  intro htr
  exact hr (hst.trans_lt htr)

/-- The GL residual is orthogonal to every earlier actual row.
Use: cancels the covariance term in the genuine transformation factorization kernel.
Article: jacobi, Proposition C.2.
Proof: the actual compressed equation makes the residual's prefix projection zero. Move that orthogonal projection onto the earlier row, which it fixes by the proved physical support. -/
theorem solutionRow_balance_inner (a : ℝ) (ha : -1<a) (t s : HalfInterval)
    (hst : (s:ℝ)≤(t:ℝ)) :
    inner ℝ (kernelRowVector a ha t+positiveOperator a ha (solutionRow a ha t))
      (solutionRow a ha s)=0 := by
  -- Compression only removes the part beyond t; the earlier row cannot see that part.
  have hp : cutoffProjection (t:ℝ) (solutionRow a ha s)=solutionRow a ha s :=
    (cutoffSubspace (t:ℝ)).starProjection_eq_self_iff.mpr (solutionRow_mem_later a ha t s hst)
  have he := solutionRow_equation a ha t
  change solutionRow a ha t+
    cutoffProjection (t:ℝ) (kernelOperator a ha (cutoffProjection (t:ℝ) (solutionRow a ha t)))=
      -(cutoffProjection (t:ℝ) (kernelRowVector a ha t)) at he
  rw [solutionRow_projected] at he
  have hz : cutoffProjection (t:ℝ)
      (kernelRowVector a ha t+positiveOperator a ha (solutionRow a ha t))=0 := by
    change cutoffProjection (t:ℝ) (kernelRowVector a ha t+
      (solutionRow a ha t+kernelOperator a ha (solutionRow a ha t)))=0
    rw [map_add,map_add,solutionRow_projected]
    rw [he,add_neg_cancel]
  calc
    _ = inner ℝ (kernelRowVector a ha t+positiveOperator a ha (solutionRow a ha t))
        (cutoffProjection (t:ℝ) (solutionRow a ha s)) := congrArg _ hp.symm
    _ = inner ℝ (cutoffProjection (t:ℝ)
        (kernelRowVector a ha t+positiveOperator a ha (solutionRow a ha t)))
        (solutionRow a ha s) := (cutoffProjection_symmetric (t:ℝ) _ _).symm
    _ = 0 := by rw [hz,inner_zero_left]

/-- The actual symmetric covariance correction vanishes on the lower half square.
Use: together with symmetry this is the pointwise cancellation for the original GL operator factorization.
Article: jacobi, Proposition C.2.
Proof: reconstruction cancels F(t,s), K(t,s), and the row pairing. The remaining three pairings are exactly the compressed residual tested against the earlier row. -/
theorem factorizationRows_zero (a : ℝ) (ha : -1<a) (t s : HalfInterval)
    (hst : (s:ℝ)≤(t:ℝ)) :
    kernel a ha (t:ℝ) (s:ℝ)+transformationKernel a ha t s+
      inner ℝ (solutionRow a ha t) (kernelRowVector a ha s)+
      inner ℝ (kernelRowVector a ha t) (solutionRow a ha s)+
      inner ℝ (positiveOperator a ha (solutionRow a ha t)) (solutionRow a ha s)=0 := by
  rw [transformationKernel,real_inner_comm (solutionRow a ha t) (kernelRowVector a ha s)]
  have h := solutionRow_balance_inner a ha t s hst
  rw [inner_add_left] at h
  linarith

/-- The continuous symmetric triangular kernel of K+K* away from the null diagonal.
Use: factorizationKernel_zero expresses the full GL factorization without discontinuous indicators.
Article: jacobi, Proposition C.2.
-/
def symmetricTransformationKernel (a : ℝ) (ha : -1<a) (t s : HalfInterval) : ℝ :=
  transformationKernel a ha (max t s) (min t s)

/-- The actual continuous covariance kernel of the GL factorization correction.
Use: its vanishing proves the operator factorization after the true integral pairings are identified.
Article: jacobi, Proposition C.2.
-/
def factorizationKernel (a : ℝ) (ha : -1<a) (t s : HalfInterval) : ℝ :=
  kernel a ha (t:ℝ) (s:ℝ)+symmetricTransformationKernel a ha t s+
    inner ℝ (solutionRow a ha t) (kernelRowVector a ha s)+
    inner ℝ (kernelRowVector a ha t) (solutionRow a ha s)+
    inner ℝ (positiveOperator a ha (solutionRow a ha t)) (solutionRow a ha s)

/-- The actual factorization correction kernel is symmetric.
Use: transfers the proved triangular cancellation to the entire square in factorizationKernel_zero.
Article: jacobi, Proposition C.2.
Proof: use source kernel symmetry, min/max commutativity and symmetry of the actual positive GL operator. -/
theorem factorizationKernel_symmetric (a : ℝ) (ha : -1<a) (t s : HalfInterval) :
    factorizationKernel a ha t s=factorizationKernel a ha s t := by
  -- Reversing the physical coordinates interchanges the two mixed row terms and preserves the positive covariance.
  unfold factorizationKernel symmetricTransformationKernel
  have hA : inner ℝ (positiveOperator a ha (solutionRow a ha t)) (solutionRow a ha s)=
      inner ℝ (solutionRow a ha t) (positiveOperator a ha (solutionRow a ha s)) :=
    positiveOperator_symmetric a ha _ _
  rw [kernel_symmetric,min_comm t s,max_comm t s,hA]
  rw [real_inner_comm (solutionRow a ha s) (kernelRowVector a ha t),
    real_inner_comm (kernelRowVector a ha s) (solutionRow a ha t),
    real_inner_comm (solutionRow a ha t) (positiveOperator a ha (solutionRow a ha s))]
  ring

/-- The original GL covariance correction is identically zero on the entire physical square.
Use: the true integral operator factorization integrates this actual kernel; no factorization hypothesis is introduced.
Article: jacobi, Proposition C.2.
Proof: on the lower triangle apply the actual compressed-row cancellation. Symmetry transfers the other triangle to that same proved case. -/
theorem factorizationKernel_zero (a : ℝ) (ha : -1<a) (t s : HalfInterval) :
    factorizationKernel a ha t s=0 := by
  -- One compressed-row cancellation handles the lower triangle; the proved symmetry handles its reflected upper triangle.
  suffices h : ∀ t s:HalfInterval,s≤t → factorizationKernel a ha t s=0 by
    rcases le_total s t with hst|hts
    · exact h t s hst
    · rw [factorizationKernel_symmetric]
      exact h s t hts
  intro t s hst
  unfold factorizationKernel symmetricTransformationKernel
  rw [max_eq_left hst,min_eq_right hst]
  exact factorizationRows_zero a ha t s hst

end
end jacobi.GelfandLevitan
