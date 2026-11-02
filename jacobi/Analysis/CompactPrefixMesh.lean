import jacobi.Analysis.PrefixMesh
import jacobi.GelfandLevitan.ShrinkingIntegral

/-!
Article: jacobi, Proposition C.3.
The actual compact continuous kernel family gives every boundedness
and moving-mesh hypothesis needed by the genuine prefix-integral limit.
Use: the actual K*F kernel products and K*f polynomial transforms in the Cholesky and eigenvector limits use this unchanged spatial integral.
-/
namespace jacobi.Analysis
noncomputable section
open Real Set Filter MeasureTheory jacobi.Reference jacobi.GelfandLevitan
open scoped Topology

/-- Continuous compact families have the genuine moving physical
prefix Riemann limit, including the zero endpoint.
Use: the actual K*F kernel products and K*f polynomial transforms in
the Cholesky and eigenvector limits use this unchanged spatial integral.
Article: jacobi, Proposition C.3.
Proof: compact continuity supplies a common actual supremum bound.
The original floor mesh converges, and the actual continuous half clamp
preserves every physical integration point. Composition gives each true
moving-mesh limit required by the established bounded prefix theorem. -/
theorem compact_prefix_mesh_limit {P:Type*} [TopologicalSpace P] [CompactSpace P]
    (G:C(P×HalfInterval,ℝ)) (p:ℕ→P) {p₀:P} (hp:Tendsto p atTop (𝓝 p₀))
    (n m:ℕ→ℕ) (hn:Tendsto n atTop atTop) (hm:∀ᶠ r:ℕ in atTop,m r≤n r)
    {t:ℝ} (ht:t∈Icc (0:ℝ) 1)
    (hmt:Tendsto (fun r:ℕ => (m r:ℝ)/(n r:ℝ)) atTop (𝓝 t)) :
    Tendsto (fun r => (∑j∈Finset.range (m r),
      G (p r,halfParameterClamp ((j:ℝ)/(n r:ℝ))))/(n r:ℝ)) atTop
      (𝓝 (∫s in (0:ℝ)..t, G (p₀,halfParameterClamp s))) := by
  apply prefix_mesh_limit n m _ _ hn hm ht hmt (norm_nonneg G)
  · exact Eventually.of_forall (fun r j => by
      simpa only [Real.norm_eq_abs] using G.norm_coe_le_norm (p r,halfParameterClamp ((j:ℝ)/(n r:ℝ))))
  · intro s hs
    have hfloor := chebyshev1.Analysis.floor_mesh_limit hn (tendsto_const_nhds (x:=s))
      (Eventually.of_forall (fun _ => hs.1.le))
    exact G.continuous.continuousAt.tendsto.comp
      (hp.prodMk_nhds (halfParameterClamp.continuous.continuousAt.tendsto.comp hfloor))

end
end jacobi.Analysis
