import jacobi.GelfandLevitan.QuotientForcingLimit

/-!
Article: jacobi, Theorem 2.1.
The derivative-forcing solution is identified with the actual right
derivative of the original constructed K. Exact original difference
quotients, true uniform-norm forcing limits and continuity of the
already proved original inverse supply the identification; no K
derivative hypothesis is introduced.
Use: continuous original derivative candidates and the right-derivative FTC upgrade this to the full closed-triangle first-coordinate C1 assertion, including its midpoint one-sided derivative.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set Filter MeasureTheory jacobi.Reference
open scoped Topology
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] kernel kernelSlope transformationKernel

/-- The actual original K has the independently constructed original derivative-forcing solution as its genuine right derivative at every positive physical parameter below the midpoint.
Use: continuous original derivative candidates and the right-derivative FTC upgrade this to the full closed-triangle first-coordinate C1 assertion, including its midpoint one-sided derivative.
Article: jacobi, Theorem 2.1.
Proof: the original exact K quotients are the genuine forced inverse reconstructions on the fixed prefix. Their original forcings converge in spatial uniform norm to the actual dot F+w*F. Apply the independently proved continuous inverse reconstruction and true continuous point evaluation. The explicit physical coordinate extensions agree throughout the actual one-sided neighborhood, so the true original slope has this same limit. -/
theorem transformationKernel_hasDerivWithinAt_right {a d : ℝ} (ha : -1<a) (hd : 0<d)
    (t s : HalfInterval) (hdt : d≤(t:ℝ)) (htop : (t:ℝ)<1/2) (hst : (s:ℝ)≤(t:ℝ)) :
    HasDerivWithinAt (fun x : ℝ => transformationKernel a ha (halfParameterClamp x) s)
      (derivativeCandidateRows ha hd ⟨(t:ℝ),⟨hdt,t.property.2⟩⟩ (halfInclusion s)) (Ici (t:ℝ)) (t:ℝ) := by
  -- The fixed-prefix inverse is applied to the true original quotient forcing, whose norm limit was proved independently of K differentiability.
  have htpos : 0<(t:ℝ) := hd.trans_le hdt
  let b := derivativeForcingRows ha hd ⟨(t:ℝ),⟨hdt,t.property.2⟩⟩
  have hcont : Continuous (fun g : C(Interval,ℝ) => forcedKernel a ha t g (halfInclusion s)) :=
    (ContinuousMap.evalCLM ℝ (halfInclusion s)).continuous.comp
      ((forcedKernel_joint_continuous a ha).comp (continuous_const.prodMk continuous_id))
  have hlim := hcont.continuousAt.tendsto.comp (quotientForcingCurve_tendsto ha hd t htpos hdt htop)
  have hvalue : forcedKernel a ha t (b.comp (prefixClamp t)) (halfInclusion s)=
      derivativeCandidateRows ha hd ⟨(t:ℝ),⟨hdt,t.property.2⟩⟩ (halfInclusion s) := by
    rw [forcedKernel_prefixClamp a ha t b (halfInclusion s) hst]
    rfl
  change Tendsto (fun x => forcedKernel a ha t (quotientForcingCurve a ha t htpos x) (halfInclusion s))
    (𝓝[>] (t:ℝ)) (𝓝 (forcedKernel a ha t (b.comp (prefixClamp t)) (halfInclusion s))) at hlim
  rw [hvalue] at hlim
  apply HasDerivWithinAt.Ici_of_Ioi
  apply (hasDerivWithinAt_iff_tendsto_slope' (lt_irrefl (t:ℝ))).mpr
  apply hlim.congr'
  filter_upwards [Ioo_mem_nhdsGT htop] with x hx
  have hself : halfParameterClamp (t:ℝ)=t := by
    apply Subtype.ext
    change ((Set.projIcc (0:ℝ) (1/2) (by norm_num) (t:ℝ)):ℝ)=(t:ℝ)
    rw [Set.projIcc_of_mem (by norm_num : (0:ℝ)≤1/2) t.property]
  have hp : halfParameterClamp x=prefixPhysicalParameter t htpos x := by
    apply Subtype.ext
    change ((Set.projIcc (0:ℝ) (1/2) (by norm_num) x):ℝ)=_
    rw [Set.projIcc_of_mem (by norm_num : (0:ℝ)≤1/2) ⟨(htpos.trans hx.1).le,hx.2.le⟩,
      prefixPhysicalParameter_val t htpos ⟨hx.1.le,hx.2.le⟩]
  have hne : prefixPhysicalParameter t htpos x≠t := by
    intro h
    have hh := congrArg Subtype.val h
    rw [prefixPhysicalParameter_val t htpos ⟨hx.1.le,hx.2.le⟩] at hh
    exact hx.1.ne' hh
  have hclamp : halfClamp (halfInclusion s)=s := by
    apply Subtype.ext
    exact min_eq_left s.property.2
  have hq := kernelDifferenceQuotient_clipped_forced a ha t (prefixPhysicalParameter t htpos x) hne (halfInclusion s) hst
  rw [← quotientForcingCurve_eq ha t htpos ⟨hx.1.le,hx.2.le⟩] at hq
  rw [← hq,kernelDifferenceQuotient_apply,prefixPhysicalParameter_val t htpos ⟨hx.1.le,hx.2.le⟩,hclamp]
  rw [slope_def_module,smul_eq_mul,hself,hp]

end
end jacobi.GelfandLevitan
