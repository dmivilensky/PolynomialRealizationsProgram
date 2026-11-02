import jacobi.GelfandLevitan.ForcedKernel

/-!
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Every genuine continuous row solving the original forced physical
prefix equation equals the independently constructed inverse solution
on that prefix. This applies in particular to actual K difference
quotients; their forcing is computed from the original GL equations.
Use: continuous_forced_unique identifies original K difference quotients with forcedKernel before taking any derivative limit.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set MeasureTheory Filter jacobi.Reference
open scoped Topology
attribute [local instance] Measure.Subtype.measureSpace
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] kernel

/-- An arbitrary continuous solution of the actual forced prefix GL equation has exactly the genuine forced inverse vector.
Use: continuous_forced_unique identifies original K difference quotients with forcedKernel before taking any derivative limit.
Article: jacobi, Theorem 2.1.
Proof: the actual prefix candidate has its exact indicator representative. Evaluate its original compressed equation almost everywhere, using the genuine kernel action and forcing representative; outside the physical prefix every term vanishes. The proved true compressed inverse gives uniqueness. -/
theorem candidateVector_eq_forced (a : ℝ) (ha : -1<a) (t : HalfInterval)
    (q b : C(Interval,ℝ))
    (hq : ∀ s : Interval,(s:ℝ)≤(t:ℝ) → q s+b s+
      (∫ r : Interval in prefixSet (t:ℝ),q r*kernel a ha (halfTime s) (halfTime r))=0) :
    candidateVector t q=forcedRow a ha t b := by
  -- The literal original continuous-row equation is tested in the same genuine physical-prefix Hilbert space.
  apply forcedRow_unique
  have hp : cutoffProjection (t:ℝ) (candidateVector t q)=candidateVector t q := cutoffProjection_idempotent _ _
  change candidateVector t q+
    cutoffProjection (t:ℝ) (kernelOperator a ha (cutoffProjection (t:ℝ) (candidateVector t q)))= -candidateVector t b
  rw [hp]
  apply Subtype.ext
  change (candidateVector t q:Space)+(cutoffProjection (t:ℝ) (kernelOperator a ha (candidateVector t q)):Space)=
    -(candidateVector t b:Space)
  apply Lp.ext
  filter_upwards [Lp.coeFn_add (candidateVector t q:Space)
      (cutoffProjection (t:ℝ) (kernelOperator a ha (candidateVector t q)):Space),
    Lp.coeFn_neg (candidateVector t b:Space),candidateVector_ae t q,candidateVector_ae t b,
    cutoffProjection_ae (t:ℝ) (kernelOperator a ha (candidateVector t q)),
    kernelOperator_ae a ha (candidateVector t q)] with s hs hn hqv hbv hP hF
  rw [hs,hn]
  change (candidateVector t q:Space) s+
    (cutoffProjection (t:ℝ) (kernelOperator a ha (candidateVector t q)):Space) s= -(candidateVector t b:Space) s
  rw [hqv,hbv,hP]
  by_cases hst : s∈prefixSet (t:ℝ)
  · have hh : s∈prefixSet (1/2) := hst.trans t.property.2
    rw [indicator_of_mem hst,indicator_of_mem hst,indicator_of_mem hst,hF,
      indicator_of_mem hh,candidateVector_action]
    linarith [hq s hst]
  · rw [indicator_of_notMem hst,indicator_of_notMem hst,indicator_of_notMem hst]
    simp only [neg_zero,zero_add]

/-- Every actual continuous solution of the original forced GL equation equals its genuine inverse reconstruction at every original prefix point.
Use: actual K difference quotients inherit convergence from the independently proved forcing and reconstruction limits, without assuming any derivative identity for K.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Proof: the actual candidate vector equals the independently constructed forced inverse. Its genuine integral action therefore agrees with the original reconstruction; the literal continuous equation gives pointwise equality throughout the physical prefix, including its null endpoints. -/
theorem continuous_forced_unique (a : ℝ) (ha : -1<a) (t : HalfInterval)
    (q b : C(Interval,ℝ))
    (hq : ∀ s : Interval,(s:ℝ)≤(t:ℝ) → q s+b s+
      (∫ r : Interval in prefixSet (t:ℝ),q r*kernel a ha (halfTime s) (halfTime r))=0)
    (s : Interval) (hs : (s:ℝ)≤(t:ℝ)) : q s=forcedKernel a ha t b s := by
  have hv := candidateVector_eq_forced a ha t q b hq
  have haction := candidateVector_action a ha t q s
  rw [hv] at haction
  change q s= -b s-kernelActionMap a ha (forcedRow a ha t b) s
  rw [haction]
  linarith [hq s hs]

end
end jacobi.GelfandLevitan
