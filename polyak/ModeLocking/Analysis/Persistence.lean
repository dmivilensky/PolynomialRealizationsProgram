import polyak.ModeLocking.Analysis.CompactCover

/-! Joint C2 continuity and fixed zero jets preserve the global symbol sign
on one parameter neighborhood, including the endpoint zero. -/
noncomputable section
namespace polyak.ModeLocking.Analysis
open Set Filter
open scoped Topology

variable {X:Type*} [TopologicalSpace X]

theorem NegativeJetCover.eventually_persist {a b:ℝ} {Z:Finset ℝ}
    {f:X→ℝ→ℝ} {p0:X} {U:Set X} (D:NegativeJetCover a b Z (f p0))
    (hp0:p0∈U)
    (hc:ContinuousOn f.uncurry (U×ˢIcc a b))
    (hc2:ContinuousOn (fun p:X×ℝ=>iteratedDeriv 2 (f p.1) p.2) (U×ˢIcc a b))
    (hsm:∀p∈U,∀x∈Icc a b,ContDiffAt ℝ 2 (f p) x)
    (hz:∀p∈U,∀z∈Z,f p z=0) (hdz:∀p∈U,∀z∈Z,deriv (f p) z=0) :
    ∀ᶠp in 𝓝[U] p0,Nonempty (NegativeJetCover a b Z (f p)) := by
  obtain ⟨V0,hV0,hbound0⟩:=isCompact_Icc.mem_uniformity_of_prod hc hp0
    (Metric.dist_mem_uniformity (show 0<D.margin/2 by positivity [D.margin_pos]))
  obtain ⟨V2,hV2,hbound2⟩:=isCompact_Icc.mem_uniformity_of_prod (f:=fun p x=>iteratedDeriv 2 (f p) x) hc2 hp0
    (Metric.dist_mem_uniformity (show 0<D.curvature/2 by positivity [D.curvature_pos]))
  filter_upwards [hV0,hV2,self_mem_nhdsWithin] with p hpV0 hpV2 hpU
  refine ⟨{
    smooth:=hsm p hpU
    centers:=D.centers
    value_zero:=hz p hpU
    slope_zero:=hdz p hpU
    radius:=D.radius
    radius_pos:=D.radius_pos
    curvature:=D.curvature/2
    curvature_pos:=by positivity [D.curvature_pos]
    margin:=D.margin/2
    margin_pos:=by positivity [D.margin_pos]
    local_bound:=by
      intro z hzZ x hx hnear
      have hh:=hbound2 p hpV2 x hx
      change dist (iteratedDeriv 2 (f p) x) (iteratedDeriv 2 (f p0) x)<D.curvature/2 at hh
      rw [Real.dist_eq,abs_lt] at hh
      have hb:=D.local_bound z hzZ x hx hnear
      linarith [hh.2]
    away_bound:=by
      intro x hx hfar
      have hh:=hbound0 p hpV0 x hx
      change dist (f p x) (f p0 x)<D.margin/2 at hh
      rw [Real.dist_eq,abs_lt] at hh
      have hb:=D.away_bound x hx hfar
      linarith [hh.2]}⟩

end polyak.ModeLocking.Analysis
