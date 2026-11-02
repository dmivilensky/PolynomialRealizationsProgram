import jacobi.GelfandLevitan.CandidateRows

/-!
Article: jacobi, Theorem 2.1.
The same proved original coercive inverse solves the inhomogeneous
physical-prefix equation for every actual continuous forcing row.
Its continuous representative, parameter continuity and stability
are the analytic inputs for applying the inverse to GL difference
quotients. Solving this equation alone does not identify a derivative.
Use: GL difference quotients and their candidate derivative are solved by this same fixed original inverse, with no new invertibility or regularity premise.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set MeasureTheory Filter jacobi.Reference
open scoped Topology InnerProductSpace
attribute [local instance] Measure.Subtype.measureSpace
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] kernel

/-- The actual original compressed inverse applied to an arbitrary genuine continuous forcing on its physical prefix.
Use: GL difference quotients and their candidate derivative are solved by this same fixed original inverse, with no new invertibility or regularity premise.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
-/
def forcedRow (a : ℝ) (ha : -1<a) (t : HalfInterval) (g : C(Interval,ℝ)) : halfSubspace :=
  -(compressedInverse a ha (t:ℝ) (candidateVector t g))

attribute [local irreducible] forcedRow candidateVector

/-- The forced original row satisfies its genuine compressed Hilbert equation.
Use: forcedRow_projected and forcedRow_spatial_equation recover exactly the original inhomogeneous physical-prefix equation.
Article: jacobi, Theorem 2.1.
Proof: apply the independently proved actual right inverse and linearity to the defining true inverse image. -/
theorem forcedRow_equation (a : ℝ) (ha : -1<a) (t : HalfInterval) (g : C(Interval,ℝ)) :
    compressedPositive a ha (t:ℝ) (forcedRow a ha t g)= -candidateVector t g := by
  rw [forcedRow,map_neg,compressedPositive_inverse_apply]

/-- The forced original row has precisely the original physical prefix support.
Use: the actual reconstructed inhomogeneous continuous row integrates only over the physical interval, as required in the differentiated original GL equation.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Proof: project the true forced compressed equation, use idempotence of the actual physical cutoff and subtract the two equalities. -/
theorem forcedRow_projected (a : ℝ) (ha : -1<a) (t : HalfInterval) (g : C(Interval,ℝ)) :
    cutoffProjection (t:ℝ) (forcedRow a ha t g)=forcedRow a ha t g := by
  -- All outer terms in the genuine compressed equation already lie in the same original physical prefix.
  have he := forcedRow_equation a ha t g
  change forcedRow a ha t g+
    cutoffProjection (t:ℝ) (kernelOperator a ha (cutoffProjection (t:ℝ) (forcedRow a ha t g)))=
      -candidateVector t g at he
  have hp := congrArg (cutoffProjection (t:ℝ)) he
  rw [map_add,map_neg,cutoffProjection_idempotent] at hp
  have hg : cutoffProjection (t:ℝ) (candidateVector t g)=candidateVector t g := by
    unfold candidateVector
    exact cutoffProjection_idempotent _ _
  rw [hg] at hp
  exact add_right_cancel (hp.trans he.symm)

/-- The actual inhomogeneous prefix solution is unique among all genuine Hilbert inputs.
Use: identifies exact original GL difference-quotient rows with the true inverse images before proving their convergence.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: the actual original compressed operator is a proved unit and hence injective; compare its two images. -/
theorem forcedRow_unique (a : ℝ) (ha : -1<a) (t : HalfInterval) (g : C(Interval,ℝ))
    (v : halfSubspace) (hv : compressedPositive a ha (t:ℝ) v= -candidateVector t g) :
    v=forcedRow a ha t g :=
  (ContinuousLinearMap.isUnit_iff_bijective.mp (compressedPositive_isUnit a ha (t:ℝ))).1
    (hv.trans (forcedRow_equation a ha t g).symm)

/-- The actual physical-prefix Hilbert embedding of continuous forcing rows is jointly continuous in its endpoint and its genuine uniform-norm input.
Use: forcedRow_joint_continuous transfers actual forcing convergence to the true inverse solutions in the unchanged original Hilbert norm.
Article: jacobi, Theorem 2.1.
Proof: the continuous-function L2 embedding and half-domain projection are bounded linear maps. Compose their continuous evaluation with the already proved genuine joint continuity of the physical cutoff. -/
theorem candidateVector_joint_continuous :
    Continuous (fun p : HalfInterval × C(Interval,ℝ) => candidateVector p.1 p.2) := by
  -- Use the true bounded continuous-to-L2 map before applying the strongly continuous moving cutoff.
  have hsource : Continuous (fun p : HalfInterval × C(Interval,ℝ) =>
      halfSubspace.orthogonalProjectionOnto (ContinuousMap.toLp (𝕜 := ℝ) (p := 2) volume p.2)) :=
    halfSubspace.orthogonalProjectionOnto.continuous.comp
      ((ContinuousMap.toLp (𝕜 := ℝ) (p := 2) volume).continuous.comp continuous_snd)
  unfold candidateVector
  exact Continuous.comp (g := fun p : ℝ × halfSubspace => cutoffProjection p.1 p.2)
    (f := fun p : HalfInterval × C(Interval,ℝ) =>
      ((p.1:ℝ),halfSubspace.orthogonalProjectionOnto
        (ContinuousMap.toLp (𝕜 := ℝ) (p := 2) volume p.2)))
    cutoffProjection_joint_continuous ((continuous_subtype_val.comp continuous_fst).prodMk hsource)

/-- The true inverse solution of the original inhomogeneous GL prefix equation varies jointly continuously with the endpoint and actual forcing in its uniform norm.
Use: the continuous genuine derivative forcing yields a continuous Hilbert candidate for partial_t K; converging original difference-quotient forcings converge to that same candidate.
Article: jacobi, Theorem 2.1.
Proof: the independently proved actual compressed inverse is norm continuous at every original endpoint. Its continuous linear evaluation on the proved jointly continuous genuine projected forcing, followed by negation, gives the assertion. -/
theorem forcedRow_joint_continuous (a : ℝ) (ha : -1<a) :
    Continuous (fun p : HalfInterval × C(Interval,ℝ) => forcedRow a ha p.1 p.2) := by
  have hi : Continuous (fun p : HalfInterval × C(Interval,ℝ) => compressedInverse a ha (p.1:ℝ)) :=
    (compressedInverse_continuous a ha).comp (continuous_subtype_val.comp continuous_fst)
  unfold forcedRow
  exact (hi.clm_apply candidateVector_joint_continuous).neg

/-- The actual original inhomogeneous solution has the literal spatial equation almost everywhere on its own physical prefix.
Use: forcedKernel_GL reconstructs its true continuous representative and the exact inhomogeneous GL equation used in the derivative argument.
Article: jacobi, Theorem 2.1.
Proof: evaluate the genuine compressed equation using only proved almost-everywhere representatives of the actual L2 operations, the original kernel operator, and the genuine physical cutoff. The projected forcing is exactly the original continuous forcing on that prefix. -/
theorem forcedRow_spatial_equation (a : ℝ) (ha : -1<a) (t : HalfInterval) (g : C(Interval,ℝ)) :
    ∀ᵐ s : Interval,(s:ℝ)≤(t:ℝ) →
      (forcedRow a ha t g:Space) s+kernelActionMap a ha (forcedRow a ha t g) s= -g s := by
  -- Genuine L2 equalities are evaluated only outside their actual representative null sets.
  have he := forcedRow_equation a ha t g
  change forcedRow a ha t g+
    cutoffProjection (t:ℝ) (kernelOperator a ha (cutoffProjection (t:ℝ) (forcedRow a ha t g)))=
      -candidateVector t g at he
  rw [forcedRow_projected] at he
  have heLp := congrArg (fun v : halfSubspace => (v:Space)) he
  change (forcedRow a ha t g:Space)+(cutoffProjection (t:ℝ) (kernelOperator a ha (forcedRow a ha t g)):Space)=
    -(candidateVector t g:Space) at heLp
  have hea := Eventually.of_forall (f := ae (volume : Measure Interval))
    (fun s : Interval => congrArg (fun v : Space => v s) heLp)
  filter_upwards [hea,Lp.coeFn_add (forcedRow a ha t g:Space)
      (cutoffProjection (t:ℝ) (kernelOperator a ha (forcedRow a ha t g)):Space),
    Lp.coeFn_neg (candidateVector t g:Space),candidateVector_ae t g,
    cutoffProjection_ae (t:ℝ) (kernelOperator a ha (forcedRow a ha t g)),
    kernelOperator_ae a ha (forcedRow a ha t g)] with s he hs hn hg hP hF
  intro hst
  have hprefix : s∈prefixSet (t:ℝ) := hst
  have hhalf : s∈prefixSet (1/2) := hst.trans t.property.2
  rw [hs,hn] at he
  change (forcedRow a ha t g:Space) s+
    (cutoffProjection (t:ℝ) (kernelOperator a ha (forcedRow a ha t g)):Space) s=
      -(candidateVector t g:Space) s at he
  rw [hg,hP,indicator_of_mem hprefix,indicator_of_mem hprefix,hF,indicator_of_mem hhalf] at he
  exact he

end
end jacobi.GelfandLevitan
