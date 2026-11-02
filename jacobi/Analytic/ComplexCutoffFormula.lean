import jacobi.Analytic.L2Compression
import jacobi.GelfandLevitan.CutoffFormula

/-!
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Complex prefix projection is exactly multiplication by the physical
interval indicator. Consequently the operator inverted in L2Inverse
acts by the original integral on (0,t), with no hidden change of domain
or measure in the zero-extension convention.
Use: identifies the actual Hilbert projection with the source spatial indicator.
-/
namespace jacobi.Analytic
noncomputable section
open Set MeasureTheory Filter jacobi.Reference jacobi.GelfandLevitan
open scoped Topology InnerProductSpace
attribute [local instance] Measure.Subtype.measureSpace
set_option backward.isDefEq.respectTransparency false

/-- The literal complex prefix cutoff of an ambient L2 input.
Use: identifies the actual Hilbert projection with the source spatial indicator.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
-/
def complexCutoffVector (t : ℝ) (v : ComplexL2) : ComplexL2 :=
  ((Lp.memLp v).indicator (prefixSet_measurable t)).toLp ((prefixSet t).indicator v)

/-- The complex cutoff has exactly the genuine physical indicator representative almost everywhere.
Use: proves orthogonal projection and the unchanged source kernel action on each interval.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Proof: apply the community MemLp-to-Lp representative theorem to the original measurable prefix indicator. -/
theorem complexCutoffVector_ae (t : ℝ) (v : ComplexL2) :
    complexCutoffVector t v =ᵐ[volume] (prefixSet t).indicator v :=
  ((Lp.memLp v).indicator (prefixSet_measurable t)).coeFn_toLp

/-- The actual complex prefix projection is precisely the physical indicator cutoff.
Use: recovers the literal original integral operator on L2(0,t) from its ambient Hilbert compression.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Proof: the literal cutoff has exactly the required tail support. The difference from the original vector is orthogonal to every prefix-supported vector, since one factor vanishes almost everywhere at every coordinate. The community orthogonal-projection characterization gives equality. -/
theorem complexProjection_ae (t : ℝ) (v : ComplexL2) :
    ((complexPrefix t).orthogonalProjectionOnto v:ComplexL2)=ᵐ[volume]
      (prefixSet t).indicator v := by
  -- All equalities of arbitrary L2 representatives are restricted to their proved common full-measure set.
  have he : (complexPrefix t).starProjection v=complexCutoffVector t v := by
    apply (complexPrefix t).eq_starProjection_of_mem_of_inner_eq_zero
    · apply (mem_complexPrefix _ _).mpr
      filter_upwards [complexCutoffVector_ae t v] with s hs
      intro hts
      rw [hs]
      exact indicator_of_notMem (show s∉prefixSet t from not_le.mpr hts) v
    · intro w hw
      rw [L2.inner_def]
      apply integral_eq_zero_of_ae
      filter_upwards [Lp.coeFn_sub v (complexCutoffVector t v),complexCutoffVector_ae t v,
        (mem_complexPrefix t w).mp hw] with s hs hc hw
      rw [hs]
      change inner ℂ (v s-complexCutoffVector t v s) (w s)=0
      rw [hc]
      by_cases hp : s∈prefixSet t
      · rw [indicator_of_mem hp,sub_self]
        exact inner_zero_left _
      · rw [indicator_of_notMem hp,hw (lt_of_not_ge hp)]
        exact inner_zero_right _
  change (complexPrefix t).starProjection v=ᵐ[volume] _
  rw [he]
  exact complexCutoffVector_ae t v

/-- On its original physical interval, the actual compressed operator acts by the literal source GL integral.
Use: ensures the inverse estimate concerns exactly I+F_t from the article, not an unrelated operator with the same bound.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Proof: combine the quotient-compatible sum representative, the exact prefix projection formula and the continuous kernel image representative. Tail support of the actual input changes its whole-domain row integral to precisely the original prefix integral. -/
theorem complexPrefixPositive_ae (F : C(KernelSquare,ℂ)) (t : ℝ) (v : complexPrefix t) :
    ∀ᵐ s:Interval,(s:ℝ)≤t →
      (complexPrefixPositive F t v:ComplexL2) s=(v:ComplexL2) s+
        ∫ r:Interval in prefixSet t,F (halfClamp s,halfClamp r)*(v:ComplexL2) r := by
  -- The ambient integration outside the source prefix is zero by the genuine input support condition.
  have hs := (mem_complexPrefix t (v:ComplexL2)).mp v.property
  filter_upwards [Lp.coeFn_add (v:ComplexL2)
    ((complexPrefix t).orthogonalProjectionOnto (complexKernelOperator F (v:ComplexL2)):ComplexL2),
    complexProjection_ae t (complexKernelOperator F (v:ComplexL2)),
    ContinuousMap.coeFn_toLp (𝕜 := ℂ) (p := 2) volume (complexKernelAction F (v:ComplexL2))]
    with s hadd hp hk
  intro hst
  change ((v:ComplexL2)+((complexPrefix t).orthogonalProjectionOnto
    (complexKernelOperator F (v:ComplexL2)):ComplexL2)) s=_
  rw [hadd,Pi.add_apply,hp,indicator_of_mem (show s∈prefixSet t from hst)]
  change (v:ComplexL2) s+ContinuousMap.toLp (𝕜 := ℂ) (p := 2) volume
    (complexKernelAction F (v:ComplexL2)) s=_
  rw [hk,complexKernelAction_apply]
  congr 1
  rw [← integral_indicator (prefixSet_measurable t)]
  apply integral_congr_ae
  filter_upwards [hs] with r hr
  by_cases hp : r∈prefixSet t
  · rw [indicator_of_mem hp]
  · rw [indicator_of_notMem hp,hr (lt_of_not_ge hp),mul_zero]

end
end jacobi.Analytic
