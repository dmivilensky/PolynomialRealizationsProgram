import jacobi.GelfandLevitan.CutoffSpace

/-!
Article: jacobi, Proposition C.2.
The abstract orthogonal projection onto the original physical interval
is exactly multiplication by its measurable indicator on the original
Lebesgue L2 space. This representative identity is used to prove strong
parameter continuity and to recover the pointwise GL equation.
Use: its measurable indicator realizes the source physical cutoff projection on the original L2 representative.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set MeasureTheory Filter jacobi.Reference
open scoped Topology InnerProductSpace
attribute [local instance] Measure.Subtype.measureSpace

/-- The original spatial prefix, including its null boundary point.
Use: its measurable indicator realizes the source physical cutoff projection on the original L2 representative.
Article: jacobi, Proposition C.2.
-/
def prefixSet (t : ℝ) : Set Interval := {s | (s:ℝ)≤t}

/-- The actual physical prefix is measurable in the original Lebesgue subtype measure.
Use: its indicator gives a original L2 input and a representative of the actual cutoff projection.
Article: jacobi, Proposition C.2.
Proof: the source coordinate is continuous, and the real lower half-line is closed. -/
theorem prefixSet_measurable (t : ℝ) : MeasurableSet (prefixSet t) :=
  (isClosed_le continuous_subtype_val continuous_const).measurableSet

/-- The original half-domain vector multiplied by the true physical prefix indicator.
Use: identifies the genuine source projection with the exact original cutoff and supplies dominated-convergence bounds.
Article: jacobi, Proposition C.2.
-/
def cutoffVector (t : ℝ) (v : halfSubspace) : halfSubspace :=
  let h := (Lp.memLp (v:Space)).indicator (prefixSet_measurable t)
  ⟨h.toLp ((prefixSet t).indicator (v:Space)),(mem_halfSubspace_iff _).mpr (by
    filter_upwards [h.coeFn_toLp,halfSubspace_supported v] with s hs hv
    intro hhalf
    rw [hs]
    by_cases hp : s∈prefixSet t
    · rw [indicator_of_mem hp,hv hhalf]
    · exact indicator_of_notMem hp _)⟩

/-- The original cutoff vector has precisely the original indicator representative almost everywhere.
Use: all original interval integrals and continuity estimates can be proved on literal source functions without evaluating an arbitrary quotient class.
Article: jacobi, Proposition C.2.
Proof: the genuine source cutoff vector is constructed by the community MemLp-to-Lp operation on this exact measurable indicator. -/
theorem cutoffVector_ae (t : ℝ) (v : halfSubspace) :
    (cutoffVector t v:Space)=ᵐ[volume] (prefixSet t).indicator (v:Space) :=
  ((Lp.memLp (v:Space)).indicator (prefixSet_measurable t)).coeFn_toLp

/-- The literal indicator cutoff is exactly the genuine orthogonal source projection.
Use: proves strong continuity of the source projections and identifies the interval-supported solution row with the original GL equation.
Article: jacobi, Proposition C.2.
Proof: the indicator vector has the exact physical support. Its
difference from the original input is orthogonal to every input with
that support, since at each point one of the two factors vanishes.
The community characterization of orthogonal projection then identifies
the original projection with this literal source vector. -/
theorem cutoffProjection_eq_vector (t : ℝ) (v : halfSubspace) :
    cutoffProjection t v=cutoffVector t v := by
  -- The orthogonality proof is on the original Lebesgue representatives and ignores only their genuine null sets.
  apply (cutoffSubspace t).eq_starProjection_of_mem_of_inner_eq_zero
  · apply (mem_cutoffSubspace_iff _ _).mpr
    filter_upwards [cutoffVector_ae t v] with s hs
    intro hts
    rw [hs]
    exact indicator_of_notMem (show s∉prefixSet t from not_le.mpr hts) (v:Space)
  · intro w hw
    change inner ℝ ((v:Space)-(cutoffVector t v:Space)) (w:Space)=0
    rw [L2.inner_def]
    apply integral_eq_zero_of_ae
    filter_upwards [Lp.coeFn_sub (v:Space) (cutoffVector t v:Space),
      cutoffVector_ae t v,(mem_cutoffSubspace_iff _ w).mp hw] with s hs hc hw
    rw [hs]
    change inner ℝ ((v:Space) s-(cutoffVector t v:Space) s) ((w:Space) s)=0
    rw [hc]
    by_cases hp : s∈prefixSet t
    · rw [indicator_of_mem hp,sub_self]
      exact inner_zero_left _
    · rw [indicator_of_notMem hp,hw (lt_of_not_ge hp)]
      exact inner_zero_right _

/-- The original source projection is literally the physical interval indicator almost everywhere.
Use: proves all parameter continuity and source integral identities for the original GL cutoff family.
Article: jacobi, Proposition C.2.
Proof: replace the original orthogonal projection by its proved actual indicator vector and use that vector's genuine representative identity. -/
theorem cutoffProjection_ae (t : ℝ) (v : halfSubspace) :
    (cutoffProjection t v:Space)=ᵐ[volume] (prefixSet t).indicator (v:Space) := by
  rw [cutoffProjection_eq_vector]
  exact cutoffVector_ae t v

end
end jacobi.GelfandLevitan
