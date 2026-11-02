import jacobi.GelfandLevitan.CutoffFormula

/-!
Article: jacobi, Proposition 2.2.
Projecting any original unit-domain L2 input onto the genuine source
half-domain is exactly multiplication by its interval indicator. The
identity makes the continuous original F action an explicit genuine
L2 representative, rather than an assertion about quotient values.
Use: gives the actual representative of the orthogonal half-domain projection used in the integral F operator.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set MeasureTheory Filter jacobi.Reference
open scoped Topology InnerProductSpace
attribute [local instance] Measure.Subtype.measureSpace

/-- An arbitrary original unit-domain L2 input restricted to the true physical half interval and zero extended.
Use: gives the actual representative of the orthogonal half-domain projection used in the integral F operator.
Article: jacobi, Proposition 2.2.
-/
def halfVector (v : Space) : halfSubspace :=
  let h := (Lp.memLp v).indicator (prefixSet_measurable (1/2))
  ⟨h.toLp ((prefixSet (1/2)).indicator v),(mem_halfSubspace_iff _).mpr (by
    filter_upwards [h.coeFn_toLp] with s hs
    intro hhalf
    rw [hs]
    exact indicator_of_notMem (show s∉prefixSet (1/2) from not_le.mpr hhalf) v)⟩

/-- The true restricted original input is represented almost everywhere by the actual physical half-interval indicator.
Use: makes the genuine half-domain projection explicit in the original spatial integral action.
Article: jacobi, Proposition 2.2.
Proof: the original restricted vector is defined by the community MemLp-to-Lp operation on precisely this source indicator function. -/
theorem halfVector_ae (v : Space) :
    (halfVector v:Space)=ᵐ[volume] (prefixSet (1/2)).indicator v :=
  ((Lp.memLp v).indicator (prefixSet_measurable (1/2))).coeFn_toLp

/-- The original half-domain orthogonal projection is the genuine physical indicator cutoff.
Use: identifies the original compact source F operator with its exact zero-extended continuous spatial representative on the half interval.
Article: jacobi, Proposition 2.2.
Proof: the true indicator vector belongs to the actual half-domain.
Its original difference from the input is orthogonal to every genuine
half-supported test vector, pointwise outside their actual null sets.
The community projection characterization proves the identity. -/
theorem halfProjection_eq_vector (v : Space) :
    halfSubspace.orthogonalProjectionOnto v=halfVector v := by
  -- The original projection is determined by real spatial orthogonality on the genuine Lebesgue domain.
  apply Subtype.ext
  apply halfSubspace.eq_starProjection_of_mem_of_inner_eq_zero (halfVector v).property
  intro w hw
  rw [L2.inner_def]
  apply integral_eq_zero_of_ae
  filter_upwards [Lp.coeFn_sub v (halfVector v:Space),halfVector_ae v,
    (mem_halfSubspace_iff w).mp hw] with s hs hc hw
  rw [hs]
  simp only [Pi.sub_apply]
  rw [hc]
  by_cases hp : s∈prefixSet (1/2)
  · rw [indicator_of_mem hp,sub_self]
    exact inner_zero_left _
  · rw [indicator_of_notMem hp,hw (lt_of_not_ge hp)]
    exact inner_zero_right _

/-- The original half-domain projection has exactly the source physical indicator representative almost everywhere.
Use: proves that the actual F image equals its genuine continuous integral formula almost everywhere at every source physical point.
Article: jacobi, Proposition 2.2.
Proof: the actual orthogonal projection equals the proved true indicator vector; use its original representative identity. -/
theorem halfProjection_ae (v : Space) :
    (halfSubspace.orthogonalProjectionOnto v:Space)=ᵐ[volume]
      (prefixSet (1/2)).indicator v := by
  rw [halfProjection_eq_vector]
  exact halfVector_ae v

/-- A continuous original spatial function has exactly its physical half-indicator representative after genuine L2 inclusion and half-domain projection.
Use: identifies both the original source F rows and its actual integral operator action without selecting point values of an arbitrary L2 quotient.
Article: jacobi, Proposition 2.2.
Proof: combine the original projection indicator formula with the community almost-everywhere representative of the genuine continuous-function L2 inclusion. -/
theorem halfProjection_toLp_ae (f : C(Interval,ℝ)) :
    (halfSubspace.orthogonalProjectionOnto
      (ContinuousMap.toLp (𝕜 := ℝ) (p := 2) volume f):Space)=ᵐ[volume]
      (prefixSet (1/2)).indicator f := by
  filter_upwards [halfProjection_ae (ContinuousMap.toLp (𝕜 := ℝ) (p := 2) volume f),
    ContinuousMap.coeFn_toLp (𝕜 := ℝ) (p := 2) volume f] with s hs hf
  rw [hs]
  by_cases hp : s∈prefixSet (1/2)
  · rw [indicator_of_mem hp,indicator_of_mem hp,hf]
  · rw [indicator_of_notMem hp,indicator_of_notMem hp]

end
end jacobi.GelfandLevitan
