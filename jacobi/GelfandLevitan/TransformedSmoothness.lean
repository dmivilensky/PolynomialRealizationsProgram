import jacobi.GelfandLevitan.TransformedDerivative

/-!
Article: jacobi, Appendix C.2.
The genuine first derivative of the actual transformed solution is
continuous on each positive physical strip. It gives the literal
community C1 predicate on (0,1/2] for every complex energy, including
the correct one-sided midpoint derivative.
Use: transformedSolution_contDiffOn localizes this to the full original domain, and the original midpoint slope is consequently the true one-sided derivative of u.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set Filter MeasureTheory jacobi.Reference
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The original transformed solution is genuinely C1 on every nondegenerate closed positive physical strip, at every complex energy.
Use: transformedSolution_contDiffOn localizes this to the full original domain, and the original midpoint slope is consequently the true one-sided derivative of u.
Article: jacobi, Appendix C.2.
Proof: the genuine derivative already proved for the original u identifies derivWithin with its independently continuous transformedSlopeRows on a domain with unique derivatives. Apply the community C1 characterization. -/
theorem transformedSolution_contDiffOn_strip {a d : ℝ} (ha : -1<a) (hd : 0<d) (hds : d<(1/2:ℝ)) (z : ℂ) :
    ContDiffOn ℝ 1 (fun x : ℝ => transformedSolution a ha (halfParameterClamp x) z) (Icc d (1/2)) := by
  -- Actual continuous derivative values determine the community derivative on the same original nondegenerate physical strip.
  let P : C(ℝ,DerivativeStrip d) := ⟨Set.projIcc d (1/2) hds.le,continuous_projIcc⟩
  let g := (transformedSlopeRows ha hd z).comp P
  have hder (x : ℝ) (hx : x∈Icc d (1/2)) :
      HasDerivWithinAt (fun y : ℝ => transformedSolution a ha (halfParameterClamp y) z) (g x) (Icc d (1/2)) x := by
    have he : g x=transformedSlopeRows ha hd z ⟨x,hx⟩ := by
      change transformedSlopeRows ha hd z (Set.projIcc d (1/2) hds.le x)=_
      rw [Set.projIcc_of_mem hds.le hx]
    rw [he]
    exact transformedSolution_hasDerivWithinAt ha hd z ⟨x,⟨(hd.trans_le hx.1).le,hx.2⟩⟩ hx.1
  apply (contDiffOn_one_iff_derivWithin (uniqueDiffOn_Icc hds)).mpr
  refine ⟨fun x hx => (hder x hx).differentiableWithinAt,?_⟩
  exact g.continuous.continuousOn.congr (fun x hx => (hder x hx).derivWithin ((uniqueDiffOn_Icc hds) x hx))

/-- The actual original transformed solution is C1 on the entire original positive half interval, including its genuine midpoint one-sided derivative, for every complex energy.
Use: supplies the fully justified original first spatial derivative for the subsequent quasi-derivative, differential equation and general operator Proposition C.2.
Article: jacobi, Appendix C.2.
Proof: every positive physical point lies in a proved C1 strip with lower endpoint half that point. This strip is a relative neighborhood in the unchanged original domain; apply community locality of continuous differentiability. -/
theorem transformedSolution_contDiffOn (a : ℝ) (ha : -1<a) (z : ℂ) :
    ContDiffOn ℝ 1 (fun x : ℝ => transformedSolution a ha (halfParameterClamp x) z) (Ioc (0:ℝ) (1/2)) := by
  intro t ht
  have hd : 0<t/2 := by linarith [ht.1]
  have hds : t/2<(1/2:ℝ) := by linarith [ht.1,ht.2]
  apply ((transformedSolution_contDiffOn_strip ha hd hds z) t ⟨by linarith [ht.1],ht.2⟩).mono_of_mem_nhdsWithin
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds (show t/2<t by linarith [ht.1]))] with x hx hlt
  exact ⟨hlt.le,hx.2⟩

end
end jacobi.GelfandLevitan
