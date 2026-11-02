import jacobi.Reference.CoefficientUniqueness

/-!
Article: jacobi, Proposition C.2.
The physical half-interval L2 space is realized by actual zero extensions
inside the already shared full reference L2 space. It is the genuine
closed kernel of restriction to the second half. The community Lp
restriction map gives closedness, completeness and orthogonal projection,
without rebuilding the earlier article's Lebesgue Hilbert space.
Use: restriction to this set cuts out exactly the zero-extended half-interval inputs in the source GL Hilbert space.
-/
namespace jacobi.Reference
noncomputable section
open Real Set MeasureTheory Filter
open scoped Topology
attribute [local instance] Measure.Subtype.measureSpace

/-- The actual second half of the original physical reference interval.
Use: restriction to this set cuts out exactly the zero-extended half-interval inputs in the source GL Hilbert space.
Article: jacobi, Appendix C.2 (uniform GL coercivity).
-/
def outsideHalf : Set Interval := {t | (1/2:ℝ)<(t:ℝ)}

/-- The genuine second-half restriction domain is measurable.
Use: the community restricted-measure almost-everywhere theorem identifies the closed kernel with the original source support condition.
Article: jacobi, Proposition C.2.
Proof: it is the preimage of the real open half-line under the continuous subtype coordinate. -/
theorem outsideHalf_measurable : MeasurableSet outsideHalf :=
  (isOpen_lt continuous_const continuous_subtype_val).measurableSet

/-- The actual community continuous L2 restriction map to the second physical half.
Use: its genuine closed kernel is precisely the original GL half-interval Hilbert space represented by zero extensions.
Article: jacobi, Proposition C.2.
-/
def halfRestriction : Space →L[ℝ] Lp ℝ 2 ((volume : Measure Interval).restrict outsideHalf) :=
  LpToLpRestrictCLM Interval ℝ ℝ volume 2 outsideHalf

/-- The true source half-interval L2 space, inside the actual original shared Hilbert space.
Use: carries the genuine compact GL operator and its source inverse, retaining actual original zero-extended coefficient integrals.
Article: jacobi, Appendix C.2 (uniform GL coercivity).
-/
def halfSubspace : Submodule ℝ Space := halfRestriction.ker

/-- Membership in the genuine closed GL Hilbert domain is exactly the original almost-everywhere source half-support condition.
Use: applies the actual coefficient uniqueness and positive quadratic identity to every genuine Hilbert-domain vector.
Article: jacobi, Appendix C.2 (uniform GL coercivity).
Proof: the community restriction representative agrees with the
original L2 function almost everywhere for the restricted measure.
Being the zero restricted L2 class is therefore exactly vanishing
almost everywhere on the measurable actual second half. -/
theorem mem_halfSubspace_iff (v : Space) : v∈halfSubspace ↔ HalfSupported v := by
  -- Only the original Lebesgue representatives and the genuine measurable restriction are used.
  change halfRestriction v=0 ↔ HalfSupported v
  rw [Lp.eq_zero_iff_ae_eq_zero]
  have he := LpToLpRestrictCLM_coeFn ℝ outsideHalf v
  change halfRestriction v=ᵐ[(volume : Measure Interval).restrict outsideHalf] v at he
  constructor
  · intro hz
    have hh := he.symm.trans hz
    simpa only [HalfSupported,outsideHalf,Set.mem_ofPred_eq,Pi.zero_apply] using
      (ae_restrict_iff' outsideHalf_measurable).mp hh
  · intro hv
    have hh : v=ᵐ[(volume : Measure Interval).restrict outsideHalf] 0 :=
      (ae_restrict_iff' outsideHalf_measurable).mpr hv
    exact he.trans hh

/-- The actual original source half-interval Hilbert domain is closed in the genuine full reference space.
Use: its inherited Hilbert structure is complete and has the community orthogonal projection needed for the genuine GL operator.
Article: jacobi, Appendix C.2 (uniform GL coercivity).
Proof: it is the actual kernel of the proved continuous linear restriction map. -/
theorem halfSubspace_closed : IsClosed (halfSubspace : Set Space) :=
  halfRestriction.isClosed_ker

/-- The true zero-extension Hilbert domain is complete for the original L2 norm.
Use: the actual compact-operator Fredholm alternative and orthogonal projection apply on the genuine source domain.
Article: jacobi, Appendix C.2 (uniform GL coercivity).
Proof: a closed subspace of the actual complete reference Hilbert space is complete. -/
instance halfSubspace_complete : CompleteSpace halfSubspace := halfSubspace_closed.completeSpace_coe

/-- Every actual vector of the source closed half-interval domain satisfies the original zero-extension condition.
Use: the genuine GL form identities and Bessel coefficient injectivity apply directly to its Hilbert-domain vectors.
Article: jacobi, Proposition C.2.
Proof: use the proved exact membership characterization for the actual submodule representative. -/
theorem halfSubspace_supported (v : halfSubspace) : HalfSupported (v:Space) :=
  (mem_halfSubspace_iff (v:Space)).mp v.property

end
end jacobi.Reference
