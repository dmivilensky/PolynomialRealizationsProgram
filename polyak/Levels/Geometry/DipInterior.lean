import polyak.Levels.Geometry.DipTopology

/-! The open dip is precisely the interior of the full closed dip. -/
noncomputable section
namespace polyak.Levels.Geometry
open General Set Filter Topology
open scoped Topology

theorem dip_isOpen (Θ : Curve) : IsOpen (dip Θ) :=
  isOpen_lt Θ.continuous (continuous_subtype_val.div_const 2)

theorem dipReal_isOpen (q : Tuning) (s : ℝ) : IsOpen (dipReal q s) := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  have hdom:=(closedDipReal_subset_phase q s ⟨hx.1,hx.2.le⟩).1
  have hcont:=(hasDerivAt_shiftedAngle q s hdom).continuousAt.sub (continuousAt_id.div_const 2)
  have he : ∀ᶠ y in 𝓝 x,shiftedAngle q s y-y/2<0:=
    hcont.eventually (eventually_lt_nhds (sub_neg.mpr hx.2))
  filter_upwards [he,isOpen_Ioo.mem_nhds hdom] with y hy hdy
  exact ⟨⟨hdy.1.le,hdy.2.le⟩,by linarith⟩

theorem interior_closedDipReal (q : Tuning) (s : ℝ) :
    interior (closedDipReal q s)=dipReal q s := by
  refine Subset.antisymm ?_ (interior_maximal (show dipReal q s⊆closedDipReal q s from fun _ h=>⟨h.1,h.2.le⟩) (dipReal_isOpen q s))
  intro x hx
  obtain ⟨δ,hδ,hball⟩:=Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hx)
  have hy : x-δ/2∈closedDipReal q s:=hball (by
    rw [Metric.mem_ball,Real.dist_eq,abs_of_nonpos (by linarith : x-δ/2-x≤0)]
    linarith)
  have hz : x+δ/2∈closedDipReal q s:=hball (by
    rw [Metric.mem_ball,Real.dist_eq,abs_of_nonneg (by linarith : 0≤x+δ/2-x)]
    linarith)
  have hh:=midpoint_mem_dipReal q s hy hz (by linarith)
  have he : (x-δ/2+(x+δ/2))/2=x:=by ring
  rwa [he] at hh

theorem interior_closedDip (q : Tuning) (s : ℝ) :
    interior (closedDip (shiftedCurve q s))=dip (shiftedCurve q s) := by
  refine Subset.antisymm ?_ (interior_maximal (show dip (shiftedCurve q s)⊆closedDip (shiftedCurve q s) from fun x h=>show shiftedCurve q s x≤(x:ℝ)/2 from (show shiftedCurve q s x<(x:ℝ)/2 from h).le) (dip_isOpen _))
  intro ω hω
  have hclosed:=interior_subset hω
  have hi:=closedDip_interior_frequency _ hclosed
  have hmap : map ((↑) : Frequency→ℝ) (𝓝 ω)=𝓝 (ω:ℝ) :=
    map_nhds_subtype_coe_eq_nhds ω.property (Icc_mem_nhds hi.1 hi.2)
  have he : (Subtype.val : Frequency→ℝ)⁻¹'closedDipReal q s=closedDip (shiftedCurve q s) := by
    ext x
    change ((x:ℝ)∈Icc 0 Real.pi ∧ shiftedAngle q s x≤(x:ℝ)/2) ↔ shiftedAngle q s x≤(x:ℝ)/2
    exact and_iff_right x.property
  have hh : closedDipReal q s∈map ((↑) : Frequency→ℝ) (𝓝 ω) := by
    change (Subtype.val : Frequency→ℝ)⁻¹'closedDipReal q s∈𝓝 ω
    rw [he]
    exact mem_interior_iff_mem_nhds.mp hω
  rw [hmap] at hh
  have hd : (ω:ℝ)∈dipReal q s:=by
    rw [←interior_closedDipReal q s]
    exact mem_interior_iff_mem_nhds.mpr hh
  exact hd.2

theorem dip_empty_of_closedDip_singleton (q : Tuning) (s : ℝ) {ω : Frequency}
    (h : closedDip (shiftedCurve q s)={ω}) : dip (shiftedCurve q s)=∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hxreal : (x:ℝ)∈dipReal q s:=⟨x.property,hx⟩
  obtain ⟨δ,hδ,hball⟩:=Metric.mem_nhds_iff.mp ((dipReal_isOpen q s).mem_nhds hxreal)
  have hy : (x:ℝ)+δ/2∈dipReal q s:=hball (by
    rw [Metric.mem_ball,Real.dist_eq,abs_of_nonneg (by linarith : 0≤(x:ℝ)+δ/2-(x:ℝ))]
    linarith)
  have hxω : x=ω:=by have hh: x∈closedDip (shiftedCurve q s):=show shiftedCurve q s x≤(x:ℝ)/2 from (show shiftedCurve q s x<(x:ℝ)/2 from hx).le; rwa [h,mem_singleton_iff] at hh
  let y : Frequency:=⟨(x:ℝ)+δ/2,hy.1⟩
  have hyω : y=ω:=by have hh: y∈closedDip (shiftedCurve q s):=hy.2.le; rwa [h,mem_singleton_iff] at hh
  have he : y=x:=hyω.trans hxω.symm
  have hre:=congrArg Subtype.val he
  change (x:ℝ)+δ/2=(x:ℝ) at hre
  linarith

/-- The entire phase-below-half-pi region is a compact interval in the
open frequency interval, including its possible empty case. -/
theorem phaseBelow_isCompact (q : Tuning) (s : ℝ) : IsCompact (phaseBelow q s) := by
  have he : phaseBelow q s=Subtype.val '' {ω : Frequency | shiftedCurve q s ω≤Real.pi/2} := by
    ext x
    constructor
    · rintro ⟨hx,hθ⟩
      exact ⟨⟨x,⟨hx.1.le,hx.2.le⟩⟩,hθ,rfl⟩
    · rintro ⟨ω,hθ,rfl⟩
      change shiftedCurve q s ω≤Real.pi/2 at hθ
      have h0 : 0<(ω:ℝ) := by
        by_contra hn
        have hz : ω=frequencyZero:=Subtype.ext (le_antisymm (le_of_not_gt hn) ω.property.1)
        rw [hz,Curve.at_zero] at hθ
        linarith [Real.pi_pos]
      have hp : (ω:ℝ)<Real.pi := by
        by_contra hn
        have hz : ω=frequencyPi:=Subtype.ext (le_antisymm ω.property.2 (le_of_not_gt hn))
        rw [hz,Curve.at_pi] at hθ
        linarith [Real.pi_pos]
      exact ⟨⟨h0,hp⟩,hθ⟩
  rw [he]
  exact ((isClosed_le (shiftedCurve q s).continuous continuous_const).isCompact).image continuous_subtype_val

end polyak.Levels.Geometry
