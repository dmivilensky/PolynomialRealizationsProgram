import polyak.ModeLocking.Boundary.PlateauEnds
import polyak.ModeLocking.Plateaus.Persistence

/-! The source closure/end statements for actual plateaus, with every
openness and fixed-support hypothesis discharged by primary regularity. -/
noncomputable section
namespace polyak.ModeLocking
open General Levels MeasureTheory Set

private def plateauCarrier (p : Plateaus.regularBoundary) : Finset Frequency :=
  Finset.univ.image (Plateaus.chosenData ⟨p.val.val,p.property⟩).atoms

private theorem plateauCarrier_coe (p : Plateaus.regularBoundary) :
    (plateauCarrier p:Set Frequency)=Plateaus.boundarySupport p := by
  ext ω
  simp only [plateauCarrier,Finset.mem_coe,Finset.mem_image,Finset.mem_univ,true_and]
  rfl

private theorem plateauCarrier_nonempty (p : Plateaus.regularBoundary) : (plateauCarrier p).Nonempty := by
  let D := Plateaus.chosenData ⟨p.val.val,p.property⟩
  exact ⟨D.atoms ⟨0,D.d_pos⟩,Finset.mem_image.mpr ⟨⟨0,D.d_pos⟩,Finset.mem_univ _,rfl⟩⟩

private theorem plateau_fixed_carrier (p : Plateaus.regularBoundary) :
    ∀ z∈Plateaus.plateau p.val, ∃ w : Measure Frequency,
      Extremal z.val w ∧ ∀ᵐω∂w,ω∈(plateauCarrier p:Set Frequency) := by
  intro z hz
  have hzreg : z∈Plateaus.regularBoundary := connectedComponentIn_subset _ _ hz
  let r : Plateaus.regularBoundary := ⟨z,hzreg⟩
  let D := Plateaus.chosenData ⟨z.val,hzreg⟩
  have he := Plateaus.support_constant_on_plateau (q := p) (r := r) hz
  refine ⟨D.measure,D.primal_feasible,?_⟩
  apply (D.measure_carried_iff _).mpr
  intro i
  rw [plateauCarrier_coe]
  rw [← he]
  exact ⟨i,rfl⟩

theorem regular_boundary_relatively_open (K : ℕ) :
    IsOpen {q : BoundaryInGap K | q.val∈Plateaus.regularTunings} :=
  Plateaus.isOpen_regularTunings.preimage continuous_subtype_val

/-- The same least period and the same finite support survive at EVERY
closure point in the gap, even when some primal weights vanish in the limit. -/
theorem source_plateau_closure {K : ℕ} (p : Plateaus.regularBoundary)
    {r : Plateaus.BoundaryTuning} (hr : r∈closure (Plateaus.plateau p.val))
    (hgap : Geometry.Gap K r.val) :
    Threshold.sigmaPeriodic r.val (Plateaus.boundaryLeastPeriod p)=0 ∧
      ∃ν : ProbabilityMeasure Frequency,ProbabilitySolution (tuningCurve r.val) nonzeroLags ν ∧
        ∀ᵐω∂(ν:Measure Frequency),ω∈Plateaus.boundarySupport p := by
  let D := Plateaus.chosenData ⟨p.val.val,p.property⟩
  have hgrid : (plateauCarrier p:Set Frequency)⊆periodicGrid (Plateaus.chosenPeriod ⟨p.val.val,p.property⟩) := by
    intro ω hω
    obtain ⟨i,_hi,rfl⟩ := Finset.mem_image.mp hω
    exact D.atoms_grid i
  obtain ⟨hperiod,ν,hν,hcar⟩ := plateau_closure_fixed_support D.period_ge
    (plateauCarrier_nonempty p) hgrid (plateau_fixed_carrier p) hr hgap
  have hleast : Plateaus.boundaryLeastPeriod p=Plateaus.chosenPeriod ⟨p.val.val,p.property⟩ :=
    Plateaus.leastPeriod_eq_chosen ⟨p.val.val,p.property⟩
  rw [hleast]
  refine ⟨hperiod,ν,hν,?_⟩
  simpa only [plateauCarrier_coe] using hcar

/-- Ambient tuning-space closure, matching the article's cl(Pi) literally. -/
theorem source_plateau_ambient_closure {K : ℕ} (p : Plateaus.regularBoundary)
    {r : Tuning}
    (hr : r∈closure ((Subtype.val : Plateaus.BoundaryTuning → Tuning) '' Plateaus.plateau p.val))
    (hbd : r∈BoundaryInGap K) :
    Threshold.sigmaPeriodic r (Plateaus.boundaryLeastPeriod p)=0 ∧
      ∃ν : ProbabilityMeasure Frequency,ProbabilitySolution (tuningCurve r) nonzeroLags ν ∧
        ∀ᵐω∂(ν:Measure Frequency),ω∈Plateaus.boundarySupport p := by
  let D := Plateaus.chosenData ⟨p.val.val,p.property⟩
  have hgrid : (plateauCarrier p:Set Frequency)⊆periodicGrid (Plateaus.chosenPeriod ⟨p.val.val,p.property⟩) := by
    intro ω hω
    obtain ⟨i,_hi,rfl⟩ := Finset.mem_image.mp hω
    exact D.atoms_grid i
  have hcar : ∀ z∈((Subtype.val : Plateaus.BoundaryTuning → Tuning) '' Plateaus.plateau p.val),
      ∃ w : Measure Frequency,Extremal z w ∧ ∀ᵐω∂w,ω∈(plateauCarrier p:Set Frequency) := by
    rintro z ⟨u,hu,rfl⟩
    exact plateau_fixed_carrier p u hu
  obtain ⟨hperiod,ν,hν,hνcar⟩ := closure_plateau_periodic D.period_ge
    (plateauCarrier_nonempty p) hgrid hcar hr hbd
  rw [show Plateaus.boundaryLeastPeriod p=Plateaus.chosenPeriod ⟨p.val.val,p.property⟩ from
    Plateaus.leastPeriod_eq_chosen ⟨p.val.val,p.property⟩]
  refine ⟨hperiod,ν,hν,?_⟩
  simpa only [plateauCarrier_coe] using hνcar

/-- The relative boundary of each actual plateau consists of periodic,
nonregular boundary points. There are no unproved topology/support premises. -/
theorem source_plateau_ends {K : ℕ} (p : Plateaus.regularBoundary)
    {r : Plateaus.BoundaryTuning} (hr : r∈frontier (Plateaus.plateau p.val))
    (hgap : Geometry.Gap K r.val) :
    PeriodicBoundary r.val ∧ r.val∉Plateaus.regularTunings := by
  have he := (source_plateau_closure p (frontier_subset_closure hr) hgap).1
  have hL : 3≤Plateaus.boundaryLeastPeriod p := by
    rw [show Plateaus.boundaryLeastPeriod p=Plateaus.chosenPeriod ⟨p.val.val,p.property⟩ from
      Plateaus.leastPeriod_eq_chosen ⟨p.val.val,p.property⟩]
    exact (Plateaus.chosenData ⟨p.val.val,p.property⟩).period_ge
  exact ⟨⟨_,hL,he⟩,frontier_component_nonregular Plateaus.isOpen_regularBoundary p.val hr⟩

end polyak.ModeLocking
