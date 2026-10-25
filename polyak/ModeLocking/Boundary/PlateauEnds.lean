import polyak.ModeLocking.Boundary.Trichotomy
import polyak.ModeLocking.Plateaus.Components

/-! Closures and relative frontier points of the actual boundary plateaus.
The topology is the source divergence boundary subtype throughout. -/
noncomputable section
namespace polyak.ModeLocking
open General Levels MeasureTheory Set

/-- Connected components of an open regular set have no regular frontier
points in a locally connected ambient space. -/
theorem frontier_component_nonregular {X : Type*} [TopologicalSpace X]
    [LocallyConnectedSpace X] {R : Set X} (hR : IsOpen R) (p : X)
    {x : X} (hx : x∈frontier (connectedComponentIn R p)) : x∉R := by
  intro hxR
  have hCompP : IsOpen (connectedComponentIn R p) := hR.connectedComponentIn
  change x∈closure (connectedComponentIn R p) ∧ x∉interior (connectedComponentIn R p) at hx
  rw [hCompP.interior_eq] at hx
  have hxC : x∈connectedComponentIn R x := mem_connectedComponentIn hxR
  have hC : IsOpen (connectedComponentIn R x) := hR.connectedComponentIn
  obtain ⟨y,hyC,hyCompP⟩ := (mem_closure_iff.mp hx.1) _ hC hxC
  have heCompP := connectedComponentIn_eq hyCompP
  have heC := connectedComponentIn_eq hyC
  apply hx.2
  rw [heCompP,←heC]
  exact hxC

/-- A fixed finite support on an actual plateau persists at every closure
point, with the same actual period and a genuine threshold probability measure. -/
theorem plateau_closure_fixed_support {K L : ℕ} {p r : Plateaus.BoundaryTuning}
    {F : Finset Frequency} (hL : 3≤L) (hF : F.Nonempty)
    (hgrid : (F:Set Frequency)⊆periodicGrid L)
    (hcar : ∀ z∈Plateaus.plateau p, ∃ w : Measure Frequency,
      Extremal z.val w ∧ ∀ᵐω∂w,ω∈(F:Set Frequency))
    (hr : r∈closure (Plateaus.plateau p)) (hgap : Geometry.Gap K r.val) :
    Threshold.sigmaPeriodic r.val L=0 ∧
      ∃ν : ProbabilityMeasure Frequency, ProbabilitySolution (tuningCurve r.val) nonzeroLags ν ∧
        ∀ᵐω∂(ν:Measure Frequency),ω∈(F:Set Frequency) := by
  have hcl : r.val∈closure ((Subtype.val : Plateaus.BoundaryTuning → Tuning) '' Plateaus.plateau p) :=
    image_closure_subset_closure_image continuous_subtype_val ⟨r,hr,rfl⟩
  have hbd : r.val∈BoundaryInGap K := ⟨r.property,hgap⟩
  apply closure_plateau_periodic hL hF hgrid (Aset :=
    ((Subtype.val : Plateaus.BoundaryTuning → Tuning) '' Plateaus.plateau p)) ?_ hcl hbd
  rintro q ⟨z,hz,rfl⟩
  exact hcar z hz

/-- This bridge separates the two independent ingredients: persistence of
the fixed finite support gives periodicity, while component topology rules
out regular endpoints. The final source wrapper uses the proved plateau APIs. -/
theorem plateau_frontier_periodic_nonregular {K L : ℕ} {p r : Plateaus.BoundaryTuning}
    {F : Finset Frequency} (hopen : IsOpen Plateaus.regularBoundary)
    (hL : 3≤L) (hF : F.Nonempty) (hgrid : (F:Set Frequency)⊆periodicGrid L)
    (hcar : ∀ z∈Plateaus.plateau p, ∃ w : Measure Frequency,
      Extremal z.val w ∧ ∀ᵐω∂w,ω∈(F:Set Frequency))
    (hr : r∈frontier (Plateaus.plateau p)) (hgap : Geometry.Gap K r.val) :
    PeriodicBoundary r.val ∧ r.val∉Plateaus.regularTunings := by
  have hcl : r∈closure (Plateaus.plateau p) := frontier_subset_closure hr
  have he := (plateau_closure_fixed_support hL hF hgrid hcar hcl hgap).1
  refine ⟨⟨L,hL,he⟩,?_⟩
  exact frontier_component_nonregular hopen p hr

end polyak.ModeLocking
