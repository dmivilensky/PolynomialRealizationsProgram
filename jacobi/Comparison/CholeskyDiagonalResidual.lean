import jacobi.Comparison.CholeskyQuadrature

/-!
Article: jacobi, Appendix C.4 (uniform Cholesky limit).
The complete same-edge discrete GL residual tends uniformly to zero on
the original physical matrix half square, including the moving row
endpoint. The cancellation is the actual previously proved GL equation.
Use: sameEdgeResidual_limit cancels the full limiting finite residual against the actual transformation kernel, without a new GL premise.
-/
namespace jacobi.Comparison
noncomputable section
open Real Set Filter MeasureTheory jacobi.Reference jacobi.Analysis jacobi.GelfandLevitan
open scoped Topology
attribute [local instance] Measure.Subtype.measureSpace
attribute [local irreducible] kernel transformationKernel

/-- The actual source GL equation has exactly its original real-prefix
integral, expressed through the genuine compact kernel-product family.
Use: sameEdgeResidual_limit cancels the full limiting finite residual
against the actual transformation kernel, without a new GL premise.
Article: jacobi, Appendix C.4 (uniform Cholesky limit).
Proof: the proved original subtype-prefix integral equals the real
physical prefix integral. Both genuine half-coordinate clamps agree
on that domain, so the established source GL equation applies exactly. -/
theorem transformationProduct_GL (a:ℝ) (ha:-1<a) (t s:HalfInterval) :
    transformationKernel a ha t s+kernel a ha (t:ℝ) (s:ℝ)+
      (∫r in (0:ℝ)..(t:ℝ), transformationProduct a a ha ha ((t,s),halfParameterClamp r))=0 := by
  have hp := prefix_integral (fun r:ℝ => transformationProduct a a ha ha ((t,s),halfParameterClamp r))
    (show (t:ℝ)∈Icc (0:ℝ) 1 from ⟨t.property.1,t.property.2.trans (by norm_num)⟩)
  change (∫r:Interval in prefixSet (t:ℝ),
    transformationKernel a ha t (halfParameterClamp (r:ℝ))*
      kernel a ha (halfParameterClamp (r:ℝ):ℝ) (s:ℝ))=_ at hp
  simp_rw [halfParameterClamp_unit,halfClamp_val] at hp
  rw [← hp]
  exact transformationKernel_GL a ha t s

/-- The literal same-edge discretized GL residual in the true original
matrix-size coordinates and the genuine original preceding-row prefix.
Use: sameEdgeResidual_uniform controls the two nonalternating terms in
the complete two-edge original Cholesky residual.
Article: jacobi, Appendix C.4 (uniform Cholesky limit).
-/
def sameEdgeResidual (a:ℝ) (ha:-1<a) (n:ℕ) (i j:Fin (n+1)) : ℝ :=
  transformationKernel a ha (matrixHalfPoint n i) (matrixHalfPoint n j)+
  kernel a ha (matrixHalfPoint n i:ℝ) (matrixHalfPoint n j:ℝ)+
  (∑l∈Finset.range i.val, transformationProduct a a ha ha
    ((matrixHalfPoint n i,matrixHalfPoint n j),halfParameterClamp ((l:ℝ)/((n:ℝ)+1))))/((n:ℝ)+1)

/-- The true same-edge residual vanishes along every cofinal original
physical row-column pair, with both actual moving spatial coordinates.
Use: sameEdgeResidual_uniform promotes the genuine moving limit to the
complete source uniform half-square assertion.
Article: jacobi, Appendix C.4 (uniform Cholesky limit).
Proof: compact continuity passes the original K and F samples to their
true limiting values. The proved actual moving-prefix mesh theorem
gives the literal remaining integral; the source GL identity is zero. -/
theorem sameEdgeResidual_limit (a:ℝ) (ha:-1<a)
    (ns:ℕ→ℕ) (hns:Tendsto ns atTop atTop) (i j:∀r:ℕ,Fin (ns r+1))
    {t s:ℝ} (ht:t∈Icc (0:ℝ) (1/2)) (hs:s∈Icc (0:ℝ) (1/2))
    (hit:Tendsto (fun r:ℕ => ((i r).val:ℝ)/(ns r:ℝ)) atTop (𝓝 t))
    (hjs:Tendsto (fun r:ℕ => ((j r).val:ℝ)/(ns r:ℝ)) atTop (𝓝 s)) :
    Tendsto (fun r => sameEdgeResidual a ha (ns r) (i r) (j r)) atTop (𝓝 0) := by
  -- Pass all three genuine residual terms to their limits before invoking the actual GL equation.
  have hp := (matrixHalfPoint_limit ns hns i ht hit).prodMk_nhds
    (matrixHalfPoint_limit ns hns j hs hjs)
  have hK := (transformationKernel_continuous a ha).continuousAt.tendsto.comp hp
  have hFc : Continuous (fun p:HalfInterval×HalfInterval => kernel a ha (p.1:ℝ) (p.2:ℝ)) :=
    ContinuousOn.comp_continuous (g:=fun p:ℝ × ℝ => kernel a ha p.1 p.2)
      (f:=fun p:HalfInterval×HalfInterval => ((p.1:ℝ),(p.2:ℝ))) (kernel_continuousOn a ha)
      ((continuous_subtype_val.comp continuous_fst).prodMk (continuous_subtype_val.comp continuous_snd))
      (fun p => ⟨p.1.property,p.2.property⟩)
  have hF := hFc.continuousAt.tendsto.comp hp
  have hS := transformationProduct_prefix_limit a a ha ha ns hns i j ht hs hit hjs
  have hh := (hK.add hF).add hS
  rw [transformationProduct_GL] at hh
  exact hh

/-- The genuine same-edge GL discretization residual vanishes uniformly
over the entire original physical matrix half square.
Use: the complete two-edge Cholesky residual combines these two true
same-edge errors with the independently vanishing alternating cross terms.
Article: jacobi, Appendix C.4 (uniform Cholesky limit).
Proof: the exact moving residual tends to zero along every cofinal pair.
The original compact physical half-square criterion supplies full
uniformity, retaining both the singular endpoint and the middle row. -/
theorem sameEdgeResidual_uniform (a:ℝ) (ha:-1<a) :
    ∀ ε:ℝ, 0<ε → ∃ N:ℕ, ∀ n≥N, ∀ i j:Fin (n+1),
      2*i.val≤n+1 → 2*j.val≤n+1 → |sameEdgeResidual a ha n i j|<ε := by
  apply half_matrix_uniform_zero (sameEdgeResidual a ha)
  intro ns hns i j _ _ t ht s hs hit hjs
  exact sameEdgeResidual_limit a ha ns hns i j ht hs hit hjs

end
end jacobi.Comparison
