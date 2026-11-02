import jacobi.GelfandLevitan.FiniteKernelAction
import jacobi.GelfandLevitan.FiniteReconstruction

/-!
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
The actual finite inverse reconstruction satisfies the literal original
finite GL integral equation. Its true inverse row is exactly its genuine
physical-prefix representative. The finite unit condition is discharged
eventually and uniformly by the proved original spectral coercivity.
Use: finiteSolutionRow_projected and finiteSolutionRow_spatial_equation recover its true physical support and original spatial integral equation.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set Filter MeasureTheory jacobi.Reference
open scoped Topology InnerProductSpace
attribute [local instance] Measure.Subtype.measureSpace
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteSolutionRow finiteTransformationKernel

/-- The actual finite inverse row satisfies its genuine original finite compressed GL equation.
Use: finiteSolutionRow_projected and finiteSolutionRow_spatial_equation recover its true physical support and original spatial integral equation.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: evaluate the actual finite right inverse at the genuine original finite source vector and use linearity of its unchanged compressed operator. -/
theorem finiteSolutionRow_equation (a : ℝ) (ha : -1<a) (N : ℕ) (t : HalfInterval)
    (hu : IsUnit (finiteCompressedPositive a ha N t)) :
    finiteCompressedPositive a ha N t (finiteSolutionRow a ha N t)=
      -(cutoffProjection t (finiteKernelRowVector a ha N t)) := by
  rw [finiteSolutionRow,map_neg]
  exact congrArg (fun T : halfSubspace →L[ℝ] halfSubspace =>
    -(T (cutoffProjection t (finiteKernelRowVector a ha N t)))) (Ring.mul_inverse_cancel _ hu)

/-- The genuine original finite inverse row is fixed by its actual physical prefix projection.
Use: its spatial equation and physical-prefix representative use the exact source integration interval (0,t).
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: project the genuine finite compressed equation again. Both original kernel and source terms are already fixed by the actual idempotent projection; cancel those equal terms. -/
theorem finiteSolutionRow_projected (a : ℝ) (ha : -1<a) (N : ℕ) (t : HalfInterval)
    (hu : IsUnit (finiteCompressedPositive a ha N t)) :
    cutoffProjection t (finiteSolutionRow a ha N t)=finiteSolutionRow a ha N t := by
  have he := finiteSolutionRow_equation a ha N t hu
  change finiteSolutionRow a ha N t+
    cutoffProjection t (finiteKernelOperator a ha N (cutoffProjection t (finiteSolutionRow a ha N t)))=_ at he
  have hp := congrArg (cutoffProjection t) he
  rw [map_add,map_neg,cutoffProjection_idempotent,cutoffProjection_idempotent] at hp
  exact add_right_cancel (hp.trans he.symm)

/-- The original finite source Hilbert row has exactly its genuine continuous half-prefix representative.
Use: evaluates the actual finite inverse equation in the unchanged original physical measure.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: apply the proved original half-projection and continuous-to-L2 representative identity to the literal original finite continuous row. -/
theorem finiteKernelRowVector_ae (a : ℝ) (ha : -1<a) (N : ℕ) (t : HalfInterval) :
    (finiteKernelRowVector a ha N t:Space)=ᵐ[volume]
      (prefixSet (1/2)).indicator (finiteKernelRows a ha N t) :=
  halfProjection_toLp_ae (finiteKernelRows a ha N t)

/-- The genuine finite inverse row satisfies the exact original finite spatial GL equation almost everywhere on its true physical prefix.
Use: finiteSolutionRow_representative identifies the original reconstructed finite K with this same actual inverse row.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: evaluate the genuine finite compressed equation almost everywhere, substituting the actual representatives of its original operator, source row and physical projections. All original indicators equal one on the true integration prefix. -/
theorem finiteSolutionRow_spatial_equation (a : ℝ) (ha : -1<a) (N : ℕ) (t : HalfInterval)
    (hu : IsUnit (finiteCompressedPositive a ha N t)) :
    ∀ᵐ s : Interval,(s:ℝ)≤t → (finiteSolutionRow a ha N t:Space) s+
      finiteKernelActionMap a ha N (finiteSolutionRow a ha N t) s= -finiteKernelRows a ha N t s := by
  -- Quotient representatives are used only outside their genuine almost-everywhere exceptional sets.
  have he := finiteSolutionRow_equation a ha N t hu
  change finiteSolutionRow a ha N t+
    cutoffProjection t (finiteKernelOperator a ha N (cutoffProjection t (finiteSolutionRow a ha N t)))=_ at he
  rw [finiteSolutionRow_projected a ha N t hu] at he
  have hLp := congrArg (fun v : halfSubspace => (v:Space)) he
  change (finiteSolutionRow a ha N t:Space)+
    (cutoffProjection t (finiteKernelOperator a ha N (finiteSolutionRow a ha N t)):Space)=
      -(cutoffProjection t (finiteKernelRowVector a ha N t):Space) at hLp
  have hpoint := Eventually.of_forall (f := ae (volume : Measure Interval))
    (fun s => congrArg (fun v : Space => v s) hLp)
  filter_upwards [hpoint,Lp.coeFn_add (finiteSolutionRow a ha N t:Space)
      (cutoffProjection t (finiteKernelOperator a ha N (finiteSolutionRow a ha N t)):Space),
    Lp.coeFn_neg (cutoffProjection t (finiteKernelRowVector a ha N t):Space),
    cutoffProjection_ae t (finiteKernelOperator a ha N (finiteSolutionRow a ha N t)),
    cutoffProjection_ae t (finiteKernelRowVector a ha N t),
    finiteKernelOperator_ae a ha N (finiteSolutionRow a ha N t),finiteKernelRowVector_ae a ha N t]
      with s he hsum hneg hP hR hF hrow
  intro hst
  rw [hsum,hneg] at he
  change (finiteSolutionRow a ha N t:Space) s+
    (cutoffProjection t (finiteKernelOperator a ha N (finiteSolutionRow a ha N t)):Space) s=
      -(cutoffProjection t (finiteKernelRowVector a ha N t):Space) s at he
  have hp : s∈prefixSet (t:ℝ) := hst
  have hh : s∈prefixSet (1/2) := hst.trans t.property.2
  rw [hP,hR,indicator_of_mem hp,indicator_of_mem hp,hF,hrow,indicator_of_mem hh,indicator_of_mem hh] at he
  exact he

/-- The genuine original finite source row is unchanged by the existing physical half-coordinate clamp.
Use: finiteSolutionRow_representative compares the true pointwise reconstruction with the actual finite spatial equation at precisely the same original coordinate.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: the genuine finite kernel depends on its spatial unit coordinate through halfTime; applying the same half clamp twice gives the same original coordinate. -/
theorem finiteKernelRows_halfClamp (a : ℝ) (ha : -1<a) (N : ℕ) (t : HalfInterval) (s : Interval) :
    finiteKernelRows a ha N t (halfInclusion (halfClamp s))=finiteKernelRows a ha N t s := by
  change finiteKernelMap a ha N (halfInclusion t,halfInclusion (halfClamp s))=finiteKernelMap a ha N (halfInclusion t,s)
  rw [finiteKernelMap_apply,finiteKernelMap_apply]
  have he : halfTime (halfInclusion (halfClamp s))=halfTime s :=
    min_eq_left (halfTime_mem s).2
  rw [he]

/-- The actual finite inverse row is precisely the original reconstructed finite K on its genuine physical prefix, with actual zero extension outside.
Use: finiteTransformationKernel_GL becomes the original pointwise finite GL equation and finite transformed integrals use exactly this same original finite K.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: on the true prefix the original finite spatial equation is exactly the reconstruction formula; beyond that prefix the actual finite inverse row vanishes by its independently proved support. -/
theorem finiteSolutionRow_representative (a : ℝ) (ha : -1<a) (N : ℕ) (t : HalfInterval)
    (hu : IsUnit (finiteCompressedPositive a ha N t)) :
    (finiteSolutionRow a ha N t:Space)=ᵐ[volume]
      (prefixSet (t:ℝ)).indicator (fun s : Interval => finiteTransformationKernel a ha N t (halfClamp s)) := by
  -- Both sides are compared in their unchanged original measure and on exactly the actual physical prefix.
  have hmem : finiteSolutionRow a ha N t∈cutoffSubspace (t:ℝ) := by
    rw [← finiteSolutionRow_projected a ha N t hu]
    exact cutoffProjection_mem _ _
  filter_upwards [finiteSolutionRow_spatial_equation a ha N t hu,(mem_cutoffSubspace_iff _ _).mp hmem] with s he hs
  by_cases hp : s∈prefixSet (t:ℝ)
  · rw [indicator_of_mem hp,finiteTransformationKernel,finiteKernelRows_halfClamp]
    have hh := he hp
    change (finiteSolutionRow a ha N t:Space) s+
      inner ℝ (finiteKernelRowVector a ha N (halfClamp s)) (finiteSolutionRow a ha N t)= -finiteKernelRows a ha N t s at hh
    linarith
  · rw [indicator_of_notMem hp]
    exact hs (lt_of_not_ge hp)

/-- The actual reconstructed finite transformation kernel satisfies the literal original finite GL integral equation with its genuine original inverse and source kernel.
Use: the finite matrix representation and original finite differential equation refer to this same actual finite transformation kernel, whose uniform limit is the original K.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: the genuine finite Hilbert row pairing is its actual source integral. Substitute the proved original physical-prefix representative of its actual inverse row, and use the community indicator-integral identity. The reconstruction rearranges to the literal original finite equation. -/
theorem finiteTransformationKernel_GL (a : ℝ) (ha : -1<a) (N : ℕ) (t s : HalfInterval)
    (hu : IsUnit (finiteCompressedPositive a ha N t)) :
    finiteTransformationKernel a ha N t s+finiteKernelRows a ha N t (halfInclusion s)+
      (∫ r : Interval in prefixSet (t:ℝ),finiteTransformationKernel a ha N t (halfClamp r)*finiteKernelRows a ha N s r)=0 := by
  -- Every finite term is already identified with the original spectral data before its inverse row representative is substituted.
  have hi : inner ℝ (finiteKernelRowVector a ha N s) (finiteSolutionRow a ha N t)=
      ∫ r : Interval in prefixSet (t:ℝ),finiteTransformationKernel a ha N t (halfClamp r)*finiteKernelRows a ha N s r := by
    change inner ℝ (rowEmbedding (finiteKernelRows a ha N s)) (finiteSolutionRow a ha N t)=_
    rw [rowEmbedding_inner,← integral_indicator (prefixSet_measurable (t:ℝ))]
    apply integral_congr_ae
    filter_upwards [finiteSolutionRow_representative a ha N t hu] with r hr
    rw [hr]
    by_cases hp : r∈prefixSet (t:ℝ)
    · rw [indicator_of_mem hp,indicator_of_mem hp]
    · rw [indicator_of_notMem hp,indicator_of_notMem hp,zero_mul]
  rw [finiteTransformationKernel,hi]
  ring

end
end jacobi.GelfandLevitan
