import jacobi.GelfandLevitan.IntegralEquation

/-!
Article: jacobi, Proposition C.2.
An arbitrary continuous spatial candidate is cut off on the actual
physical prefix. Its exact representative identifies the literal GL
integral with the genuine compressed Hilbert equation. Actual inverse
uniqueness therefore determines the candidate, with no completeness,
spectral or invertibility hypotheses supplied by the candidate.
Use: compares every literal continuous GL candidate with the already constructed true inverse solution, proving uniqueness of the original kernel.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set MeasureTheory Filter jacobi.Reference
open scoped Topology InnerProductSpace
attribute [local instance] Measure.Subtype.measureSpace
attribute [local irreducible] kernel

/-- The genuine Hilbert vector of an arbitrary continuous source row on its actual physical prefix.
Use: compares every literal continuous GL candidate with the already constructed true inverse solution, proving uniqueness of the original kernel.
Article: jacobi, Proposition C.2.
-/
def candidateVector (t : HalfInterval) (g : C(Interval,ℝ)) : halfSubspace :=
  cutoffProjection (t:ℝ) (halfSubspace.orthogonalProjectionOnto
    (ContinuousMap.toLp (𝕜 := ℝ) (p := 2) volume g))

/-- An arbitrary genuine candidate vector has its exact original physical-prefix indicator representative.
Use: converts its actual source integrals and compressed Hilbert equation into the literal GL equation of the continuous candidate.
Article: jacobi, Proposition C.2.
Proof: apply the true cutoff representative and the actual half-space
projection representative. On the physical prefix the half indicator
is one, while outside the prefix the actual cutoff is already zero. -/
theorem candidateVector_ae (t : HalfInterval) (g : C(Interval,ℝ)) :
    (candidateVector t g:Space)=ᵐ[volume] (prefixSet (t:ℝ)).indicator g := by
  filter_upwards [cutoffProjection_ae (t:ℝ) (halfSubspace.orthogonalProjectionOnto
      (ContinuousMap.toLp (𝕜 := ℝ) (p := 2) volume g)),halfProjection_toLp_ae g] with s hs hg
  change (candidateVector t g:Space) s=_ at hs
  rw [hs]
  by_cases hp : s∈prefixSet (t:ℝ)
  · have hh : s∈prefixSet (1/2) := hp.trans t.property.2
    rw [indicator_of_mem hp,indicator_of_mem hp,hg,indicator_of_mem hh]
  · rw [indicator_of_notMem hp,indicator_of_notMem hp]

/-- Integrating an arbitrary genuine candidate vector is exactly integrating its continuous row over the original physical prefix.
Use: rewrites the true kernel action on the candidate as the literal interval integral appearing in its source GL equation.
Article: jacobi, Proposition C.2.
Proof: replace the genuine source vector by its proved exact physical indicator representative and apply the community indicator integral identity. -/
theorem candidateVector_integral (t : HalfInterval) (g : C(Interval,ℝ)) (h : Interval → ℝ) :
    (∫ r:Interval,(candidateVector t g:Space) r*h r)=
      ∫ r:Interval in prefixSet (t:ℝ),g r*h r := by
  rw [← integral_indicator (prefixSet_measurable (t:ℝ))]
  apply integral_congr_ae
  filter_upwards [candidateVector_ae t g] with r hr
  rw [hr]
  by_cases hp : r∈prefixSet (t:ℝ)
  · rw [indicator_of_mem hp,indicator_of_mem hp]
  · rw [indicator_of_notMem hp,indicator_of_notMem hp,zero_mul]

/-- The original kernel action on an arbitrary candidate is precisely its literal physical-prefix GL integral.
Use: every continuous candidate satisfying the original source equation also satisfies the genuine compressed Hilbert inverse equation.
Article: jacobi, Proposition C.2.
Proof: the genuine continuous kernel action is a true source row pairing, already identified with its original integral. The exact candidate indicator formula restricts that integral to the actual prefix. -/
theorem candidateVector_action (a : ℝ) (ha : -1<a) (t : HalfInterval)
    (g : C(Interval,ℝ)) (s : Interval) :
    kernelActionMap a ha (candidateVector t g) s=
      ∫ r:Interval in prefixSet (t:ℝ),g r*kernel a ha (halfTime s) (halfTime r) := by
  change inner ℝ (kernelRowVector a ha (halfClamp s)) (candidateVector t g)=_
  rw [kernelRowVector_inner]
  exact candidateVector_integral t g _

/-- Every arbitrary continuous row satisfying the literal original GL equation gives exactly the actual inverse solution vector.
Use: proves uniqueness of the original continuous transformation kernel without adding any unproved analytic or spectral condition on the candidate.
Article: jacobi, Proposition C.2.
Proof: the genuine candidate is fixed by the actual physical projection.
The literal source equation and true integral-action representative show
that its compressed image equals the actual source right-hand side,
almost everywhere on the prefix; all terms vanish outside. The proved
genuine inverse uniqueness identifies it with the original k_t. -/
theorem candidateVector_eq_solution (a : ℝ) (ha : -1<a) (t : HalfInterval)
    (g : C(Interval,ℝ))
    (hg : ∀ s:Interval,(s:ℝ)≤(t:ℝ) → g s+kernelRows a ha t s+
      (∫ r:Interval in prefixSet (t:ℝ),g r*kernel a ha (halfTime s) (halfTime r))=0) :
    candidateVector t g=solutionRow a ha t := by
  -- The arbitrary candidate is tested in the original Hilbert space, using the exact source representatives.
  apply solutionRow_unique
  have hp : cutoffProjection (t:ℝ) (candidateVector t g)=candidateVector t g :=
    cutoffProjection_idempotent _ _
  change candidateVector t g+
    cutoffProjection (t:ℝ) (kernelOperator a ha (cutoffProjection (t:ℝ) (candidateVector t g)))=
      -(cutoffProjection (t:ℝ) (kernelRowVector a ha t))
  rw [hp]
  apply Subtype.ext
  change (candidateVector t g:Space)+
    (cutoffProjection (t:ℝ) (kernelOperator a ha (candidateVector t g)):Space)=
      -(cutoffProjection (t:ℝ) (kernelRowVector a ha t):Space)
  apply Lp.ext
  filter_upwards [Lp.coeFn_add (candidateVector t g:Space)
      (cutoffProjection (t:ℝ) (kernelOperator a ha (candidateVector t g)):Space),
    Lp.coeFn_neg (cutoffProjection (t:ℝ) (kernelRowVector a ha t):Space),
    candidateVector_ae t g,
    cutoffProjection_ae (t:ℝ) (kernelOperator a ha (candidateVector t g)),
    cutoffProjection_ae (t:ℝ) (kernelRowVector a ha t),
    kernelOperator_ae a ha (candidateVector t g),kernelRowVector_ae a ha t]
    with s hs hn hv hP hQ hF hR
  rw [hs,hn]
  simp only [Pi.add_apply,Pi.neg_apply]
  rw [hv,hP,hQ]
  by_cases hst : s∈prefixSet (t:ℝ)
  · have hh : s∈prefixSet (1/2) := hst.trans t.property.2
    rw [indicator_of_mem hst,indicator_of_mem hst,indicator_of_mem hst,hF,hR,
      indicator_of_mem hh,indicator_of_mem hh,candidateVector_action]
    linarith [hg s hst]
  · rw [indicator_of_notMem hst,indicator_of_notMem hst,indicator_of_notMem hst]
    simp only [neg_zero,zero_add]

/-- Every original continuous candidate row satisfying the literal GL equation equals the actually reconstructed kernel throughout its true physical prefix.
Use: the original pointwise GL solution is unique, not just its Hilbert equivalence class; this fixes all subsequent transformed solutions and endpoint values.
Article: jacobi, Proposition C.2.
Proof: its actual prefix vector is the proved genuine inverse solution.
Pair that same vector with the true source row and use the actual
candidate integral formula. The original reconstruction and the literal
candidate equation then have exactly the same integral, giving pointwise
equality at every actual physical point, including the endpoints. -/
theorem continuous_row_unique (a : ℝ) (ha : -1<a) (t : HalfInterval)
    (g : C(Interval,ℝ))
    (hg : ∀ s:Interval,(s:ℝ)≤(t:ℝ) → g s+kernelRows a ha t s+
      (∫ r:Interval in prefixSet (t:ℝ),g r*kernel a ha (halfTime s) (halfTime r))=0)
    (s : HalfInterval) (hst : (s:ℝ)≤(t:ℝ)) :
    g (halfInclusion s)=transformationKernel a ha t s := by
  -- The exact original integral equation upgrades Hilbert uniqueness to equality at every source spatial point.
  have hv := candidateVector_eq_solution a ha t g hg
  have he := transformationKernel_reconstruction a ha t s
  rw [← hv,candidateVector_integral] at he
  have hc := hg (halfInclusion s) hst
  rw [kernelRows_apply] at hc
  have ht : halfTime (halfInclusion s)=(s:ℝ) := min_eq_left s.property.2
  rw [ht] at hc
  have hi : (∫ r:Interval in prefixSet (t:ℝ),g r*kernel a ha (s:ℝ) (halfTime r))=
      ∫ r:Interval in prefixSet (t:ℝ),g r*kernel a ha (halfTime r) (s:ℝ) := by
    apply integral_congr_ae
    exact Eventually.of_forall (fun r => by dsimp only; rw [kernel_symmetric])
  rw [hi] at hc
  linarith

end
end jacobi.GelfandLevitan
