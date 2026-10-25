import polyak.Levels.Geometry.Convexity
import Mathlib.Analysis.Convex.Topology

/-! Topology of the complete closed dip, including the singleton case. -/
noncomputable section
namespace polyak.Levels.Geometry
open General Set Topology

 theorem closedDipReal_subset_phase (q : Tuning) (s : ℝ) :
    closedDipReal q s⊆phaseBelow q s := by
  intro ω hω
  have hh : (⟨ω,hω.1⟩:Frequency)∈closedDip (shiftedCurve q s):=hω.2
  exact ⟨closedDip_interior_frequency _ hh,by linarith [hω.1.2,hω.2]⟩

 theorem midpoint_mem_dipReal (q : Tuning) (s : ℝ) {x y : ℝ}
    (hx : x∈closedDipReal q s) (hy : y∈closedDipReal q s) (hne : x≠y) :
    (x+y)/2∈dipReal q s := by
  have hp := (phase_line_strictConvexOn q s 1 0).lt_on_open_segment'
    (closedDipReal_subset_phase q s hx) (closedDipReal_subset_phase q s hy) hne
    (a:= (1:ℝ)/2) (b:=(1:ℝ)/2) (by norm_num) (by norm_num) (by norm_num)
  have hc : (x+y)/2∈closedDipReal q s := by
    convert (closedDipReal_convex q s) hx hy (by norm_num : (0:ℝ)≤1/2)
      (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1:ℝ)/2+1/2=1) using 1
    simp only [smul_eq_mul]
    ring
  refine ⟨hc.1,?_⟩
  have hm : max (shiftedAngle q s x-x/2) (shiftedAngle q s y-y/2)≤0 :=
    max_le (by linarith [hx.2]) (by linarith [hy.2])
  simp only [one_mul,mul_zero,sub_zero,smul_eq_mul] at hp
  have he : (1:ℝ)/2*x+1/2*y=(x+y)/2:=by ring
  rw [he] at hp
  linarith

 theorem closedDip_nonsingleton_imp_dip_nonempty (q : Tuning) (s : ℝ)
    {x y : Frequency} (hx : x∈closedDip (shiftedCurve q s))
    (hy : y∈closedDip (shiftedCurve q s)) (hne : x≠y) :
    (dip (shiftedCurve q s)).Nonempty := by
  have hm := midpoint_mem_dipReal q s ⟨x.property,hx⟩ ⟨y.property,hy⟩
    (fun he=>hne (Subtype.ext he))
  exact ⟨⟨((x:ℝ)+(y:ℝ))/2,hm.1⟩,hm.2⟩

 theorem closedDip_singleton_of_dip_empty (q : Tuning) (s : ℝ)
    (hc : (closedDip (shiftedCurve q s)).Nonempty)
    (hd : dip (shiftedCurve q s)=∅) :
    ∃ω : Frequency,closedDip (shiftedCurve q s)={ω} := by
  obtain ⟨ω,hω⟩:=hc
  refine ⟨ω,Set.Subset.antisymm ?_ (singleton_subset_iff.mpr hω)⟩
  intro x hx
  rw [mem_singleton_iff]
  by_contra hne
  have hh:=closedDip_nonsingleton_imp_dip_nonempty q s hx hω hne
  simp only [hd,Set.not_nonempty_empty] at hh

 theorem closedDipReal_eq_closure_dipReal (q : Tuning) (s : ℝ)
    (hd : (dipReal q s).Nonempty) : closedDipReal q s=closure (dipReal q s) := by
  have hclosed : IsClosed (closedDipReal q s) := by
    have he : closedDipReal q s=Subtype.val '' closedDip (shiftedCurve q s) := by
      ext ω
      constructor
      · rintro ⟨hω,hθ⟩
        exact ⟨⟨ω,hω⟩,hθ,rfl⟩
      · rintro ⟨ω,hω,rfl⟩
        exact ⟨ω.property,hω⟩
    rw [he]
    exact ((closedDip_isCompact _).image continuous_subtype_val).isClosed
  refine Subset.antisymm ?_ (closure_minimal (fun _ h=>⟨h.1,h.2.le⟩) hclosed)
  obtain ⟨y,hy⟩:=hd
  intro x hx
  by_cases he : x=y
  · subst x
    exact subset_closure hy
  have hseg : openSegment ℝ x y⊆dipReal q s := by
    intro z hz
    have hp:=(phase_line_strictConvexOn q s 1 0).lt_on_openSegment
      (closedDipReal_subset_phase q s hx) (closedDipReal_subset_phase q s ⟨hy.1,hy.2.le⟩) he hz
    have hc:=(closedDipReal_convex q s).segment_subset hx ⟨hy.1,hy.2.le⟩ (openSegment_subset_segment ℝ x y hz)
    have hm : max (shiftedAngle q s x-x/2) (shiftedAngle q s y-y/2)≤0 :=
      max_le (by linarith [hx.2]) (by linarith [hy.2])
    simp only [one_mul,mul_zero,sub_zero] at hp
    exact ⟨hc.1,by linarith⟩
  exact closure_mono hseg (segment_subset_closure_openSegment (left_mem_segment ℝ x y))

theorem closedDip_eq_closure_dip (q : Tuning) (s : ℝ)
    (hd : (dip (shiftedCurve q s)).Nonempty) :
    closedDip (shiftedCurve q s)=closure (dip (shiftedCurve q s)) := by
  have he : Subtype.val '' dip (shiftedCurve q s)=dipReal q s := by
    ext ω
    constructor
    · rintro ⟨ω,hω,rfl⟩
      exact ⟨ω.property,hω⟩
    · rintro ⟨hω,hθ⟩
      exact ⟨⟨ω,hω⟩,hθ,rfl⟩
  have hd' : (dipReal q s).Nonempty := by
    obtain ⟨ω,hω⟩:=hd
    exact ⟨ω,ω.property,hω⟩
  rw [IsEmbedding.subtypeVal.closure_eq_preimage_closure_image,he,
    ←closedDipReal_eq_closure_dipReal q s hd']
  ext ω
  change shiftedAngle q s ω≤(ω:ℝ)/2 ↔ ((ω:ℝ)∈Icc 0 Real.pi ∧ shiftedAngle q s ω≤(ω:ℝ)/2)
  exact (and_iff_right ω.property).symm

end polyak.Levels.Geometry
