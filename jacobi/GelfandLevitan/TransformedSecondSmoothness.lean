import jacobi.GelfandLevitan.TransformedEquation

/-!
Article: jacobi, Appendix C.2.
Use: transformedSolution_contDiffOn_two_strip obtains the actual C2 predicate for the same original GL solution, including its genuine midpoint derivative.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set Filter jacobi.Reference
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The actual original transformed slope is genuinely C1 on every positive physical strip, with its genuine second derivative prescribed by the original transformed ODE.
Use: transformedSolution_contDiffOn_two_strip obtains the actual C2 predicate for the same original GL solution, including its genuine midpoint derivative.
Article: jacobi, Appendix C.2.
Proof: the proved original transformed ODE identifies its true slope derivative with the continuous original potential/solution product. Unique derivatives on the nondegenerate physical strip and the community C1 characterization give the result. -/
theorem transformedSlope_contDiffOn_one_strip (a : ℝ) (ha : -1<a) {d : ℝ} (hd : 0<d)
    (hds : d<(1/2:ℝ)) (z : ℂ) :
    ContDiffOn ℝ 1 (stripExtension hds.le (transformedSlopeRows ha hd z)) (Icc d (1/2)) := by
  -- The derivative is the actual original differential-equation value, already proved for the genuine GL slope.
  let A := (stripComplex (transformedPotentialStrip a ha hd hds.le)-ContinuousMap.const _ z)*
    transformedSolutionStrip a ha hd z
  have hD (t : ℝ) (ht : t∈Icc d (1/2)) :
      HasDerivWithinAt (stripExtension hds.le (transformedSlopeRows ha hd z))
        (stripExtension hds.le A t) (Icc d (1/2)) t := by
    rw [show t=(⟨t,ht⟩:ClosedStrip d (1/2)).val from rfl,stripExtension_value]
    simpa only [A,ContinuousMap.mul_apply,ContinuousMap.sub_apply,ContinuousMap.const_apply,stripComplex_apply] using
      transformedSolution_ODE_strip a ha hd hds z ⟨t,ht⟩
  apply (contDiffOn_one_iff_derivWithin (uniqueDiffOn_Icc hds)).mpr
  refine ⟨fun t ht => (hD t ht).differentiableWithinAt,?_⟩
  exact (stripExtension hds.le A).continuous.continuousOn.congr
    (fun t ht => (hD t ht).derivWithin ((uniqueDiffOn_Icc hds) t ht))

/-- The actual original GL transformed solution is genuinely C2 on every closed positive physical strip, including the midpoint one-sided derivative.
Use: transformedSolution_contDiffOn_two localizes the result to the entire positive physical half interval, completing the original regularity assertion needed by Proposition C.2's differential-operator realization.
Article: jacobi, Appendix C.2.
Proof: the already identified original first derivative equals the genuine transformed slope on the whole physical strip. That same actual slope is C1 by the original transformed ODE. The community successor characterization therefore gives C2 for the unchanged original GL solution. -/
theorem transformedSolution_contDiffOn_two_strip (a : ℝ) (ha : -1<a) {d : ℝ} (hd : 0<d)
    (hds : d<(1/2:ℝ)) (z : ℂ) :
    ContDiffOn ℝ 2 (fun x : ℝ => transformedSolution a ha (halfParameterClamp x) z) (Icc d (1/2)) := by
  -- The continuous-differentiability predicate is applied to the original function, not an ODE solution introduced independently.
  have hD (t : ℝ) (ht : t∈Icc d (1/2)) :=
    transformedSolution_hasDerivWithinAt ha hd z ⟨t,⟨(hd.trans_le ht.1).le,ht.2⟩⟩ ht.1
  have hEq : EqOn (stripExtension hds.le (transformedSlopeRows ha hd z))
      (derivWithin (fun x : ℝ => transformedSolution a ha (halfParameterClamp x) z) (Icc d (1/2))) (Icc d (1/2)) := by
    intro t ht
    rw [show t=(⟨t,ht⟩:ClosedStrip d (1/2)).val from rfl,stripExtension_value]
    exact ((hD t ht).derivWithin ((uniqueDiffOn_Icc hds) t ht)).symm
  apply (contDiffOn_succ_iff_derivWithin (n := 1) (uniqueDiffOn_Icc hds)).mpr
  exact ⟨fun t ht => (hD t ht).differentiableWithinAt,by norm_num,
    (transformedSlope_contDiffOn_one_strip a ha hd hds z).congr hEq.symm⟩

/-- The actual original GL transformed solution is genuinely C2 on the entire positive physical half interval at every complex energy.
Use: supplies Proposition C.2's actual transformed differential regularity, with the original midpoint left derivatives retained for the boundary characteristics and target operator.
Article: jacobi, Appendix C.2.
Proof: every positive physical point has a nondegenerate proved C2 strip whose lower endpoint is half that point. This strip is a relative neighborhood in the actual original domain, so the community locality theorem gives the full original C2 statement. -/
theorem transformedSolution_contDiffOn_two (a : ℝ) (ha : -1<a) (z : ℂ) :
    ContDiffOn ℝ 2 (fun x : ℝ => transformedSolution a ha (halfParameterClamp x) z) (Ioc (0:ℝ) (1/2)) := by
  -- The strip includes the midpoint, so localization preserves the original one-sided upper boundary regularity.
  intro t ht
  have hd : 0<t/2 := by linarith [ht.1]
  have hds : t/2<(1/2:ℝ) := by linarith [ht.1,ht.2]
  apply ((transformedSolution_contDiffOn_two_strip a ha hd hds z) t ⟨by linarith [ht.1],ht.2⟩).mono_of_mem_nhdsWithin
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds (show t/2<t by linarith [ht.1]))] with x hx hlt
  exact ⟨hlt.le,hx.2⟩

end
end jacobi.GelfandLevitan
