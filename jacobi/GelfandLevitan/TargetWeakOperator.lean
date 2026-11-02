import jacobi.GelfandLevitan.TargetTestDomain

/-!
Article: jacobi, Theorem 2.1.
The actual unbounded spectral operator has the original Schrodinger action
distributionally on its entire domain. Compact C2 tests already belong to
that domain with the classical action, so formal self-adjointness supplies
the full-domain assertion without additional endpoint assumptions.
Source: the adjoint definition of the distributional differential expression.
Use: targetOperator_weak_action completes the full differential realization
of the same operator whose original Green inverse and finite limits are proved.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set Filter Function MeasureTheory jacobi.Reference
open scoped Topology InnerProductSpace
attribute [local instance] Measure.Subtype.measureSpace

/-- The genuine target operator acts as the original Schrodinger expression
distributionally on every element of its full weighted spectral domain.
Use: completes the operator assertion of Theorem 2.1, extending the proved
classical compact-test action to the entire self-adjoint realization.
Article: jacobi, Proposition C.2.
Proof: every compact C2 test is in the actual operator graph. The already
proved formal self-adjointness transfers the operator to that test; the
actual continuous representatives then give the two displayed integrals. -/
theorem targetOperator_weak_action (a : ℝ) (ha : -1<a) (v : (targetOperator a ha).domain)
    {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g) (hc : HasCompactSupport g)
    (hs : tsupport g ⊆ Ioo (0:ℝ) 1) :
    (∫ t : Interval,(targetOperator a ha v) t*g t)=
      ∫ t : Interval,(v:Space) t*testExpression a ha g t := by
  obtain ⟨hdom,hact⟩ := targetOperator_compact_test a ha hg hc hs
  let G := physicalTestMap g hg.continuous
  let Q := physicalTestMap (testExpression a ha g) (testExpression_continuous a ha hg hs)
  have hi := chebyshev2.Continuum.unboundedDiagonalOperator_symmetric
    (fullTargetBasis a ha) (jacobi.Bessel.sigma a ha)
    ⟨ContinuousMap.toLp (𝕜 := ℝ) (p := 2) volume G,hdom⟩ v
  change inner ℝ (targetOperator a ha ⟨ContinuousMap.toLp (𝕜 := ℝ) (p := 2) volume G,hdom⟩)
    (v:Space)=inner ℝ (ContinuousMap.toLp (𝕜 := ℝ) (p := 2) volume G) (targetOperator a ha v) at hi
  rw [hact,L2.inner_def,L2.inner_def] at hi
  have hleft : (∫ t : Interval,(targetOperator a ha v) t*g t)=
      ∫ t : Interval,(targetOperator a ha v) t*(ContinuousMap.toLp (𝕜 := ℝ) (p := 2) volume G) t := by
    apply integral_congr_ae
    filter_upwards [ContinuousMap.coeFn_toLp (𝕜 := ℝ) (p := 2) volume G] with t ht
    rw [ht]
    rfl
  have hright : (∫ t : Interval,(v:Space) t*testExpression a ha g t)=
      ∫ t : Interval,(v:Space) t*(ContinuousMap.toLp (𝕜 := ℝ) (p := 2) volume Q) t := by
    apply integral_congr_ae
    filter_upwards [ContinuousMap.coeFn_toLp (𝕜 := ℝ) (p := 2) volume Q] with t ht
    rw [ht]
    rfl
  rw [hleft,hright]
  exact hi.symm

end
end jacobi.GelfandLevitan
