import polyak.ModeLocking.Plateaus.TightClasses
import polyak.ModeLocking.Plateaus.FixedDeterminant
import polyak.ModeLocking.Plateaus.Projection
import polyak.ModeLocking.Plateaus.Anchors
import polyak.ModeLocking.Modelock.Boundary

/-! The source plateau conclusions use the actual open connected components,
all finite Borel extremals, and the intrinsic support, period and classes. -/
noncomputable section
namespace polyak.ModeLocking.Plateaus
open General Levels Geometry Set Filter MeasureTheory
open scoped Topology

/-- Every component keeps all three source labels, independently of the
choice and ordering of any regular certificate. -/
theorem plateau_labels {q r : regularBoundary} (hr : r.val∈plateau q.val) :
    boundarySupport r=boundarySupport q ∧ boundaryLeastPeriod r=boundaryLeastPeriod q ∧
      boundaryActiveClasses r=boundaryActiveClasses q :=
  ⟨support_constant_on_plateau hr,leastPeriod_constant_on_plateau hr,activeClasses_constant_on_plateau hr⟩

/-- At each point of a plateau the same finite support and tight residue
sets give the original square determinant equation at shift zero. -/
theorem plateau_regular_data {q r : regularBoundary} (hr : r.val∈plateau q.val) :
    ∃R : RegularData r.val.val 0 (boundaryLeastPeriod q),
      Set.range R.atoms=boundarySupport q ∧ Set.range R.reps=boundaryActiveClasses q ∧
      Continuation.tightDeterminant R.reps R.atoms (Continuation.sourcePoint r.val.val 0)=0 := by
  let p : RegularTuning:=⟨r.val.val,r.property⟩
  let R := chosenData p
  have hS : Set.range R.atoms=boundarySupport q := support_constant_on_plateau hr
  have hA : Set.range R.reps=boundaryActiveClasses q :=
    (activeClasses_eq p.property R).symm.trans (activeClasses_constant_on_plateau hr)
  have hL : chosenPeriod p=boundaryLeastPeriod q :=
    (leastPeriod_eq_chosen p).symm.trans (leastPeriod_constant_on_plateau hr)
  have hex : ∃R' : RegularData r.val.val (Threshold.sigma r.val.val) (chosenPeriod p),
      Set.range R'.atoms=boundarySupport q ∧ Set.range R'.reps=boundaryActiveClasses q ∧
      Continuation.tightDeterminant R'.reps R'.atoms
        (Continuation.sourcePoint r.val.val (Threshold.sigma r.val.val))=0 :=
    ⟨R,hS,hA,R.tightDeterminant_zero⟩
  rw [(mem_frontier_iff_sigma_zero r.val.val).mp r.val.property,hL] at hex
  exact hex

/-- The actual boundary has an analytic graph at every point of a plateau. -/
theorem regular_boundary_analytic_graph (r : regularBoundary) :
    ∃g:Gradient.Plane→ℝ,AnalyticAt ℝ g (Gradient.planeParameters r.val.val) ∧
      g (Gradient.planeParameters r.val.val)=r.val.val.kappa ∧
      ∃U:Set Tuning,IsOpen U ∧ r.val.val∈U ∧ ∀q'∈U,
        q'∈frontier Regions.divergenceSet ↔g (Gradient.planeParameters q')=q'.kappa :=
  (chosenData ⟨r.val.val,r.property⟩).analytic_divergence_boundary
    ((mem_frontier_iff_sigma_zero r.val.val).mp r.val.property)

/-- If exactly one support atom lies in the fixed gap window, it is the
unique positive-mass closed-dip anchor of every actual extremal throughout
the entire part of the plateau in that gap. -/
theorem plateau_unique_anchor {q r : regularBoundary} (hr : r.val∈plateau q.val)
    {K : ℕ} (hgap : Gap K r.val.val) {star : Frequency}
    (honly : ∀ω∈boundarySupport q,InWindow K ω→ω=star)
    {w : Measure Frequency} (hw : ProgramSolution (tuningCurve r.val.val) nonzeroLags w) :
    ∀ω : Frequency,Farey.Anchor r.val.val w ω ↔ω=star := by
  let R := chosenData (⟨r.val.val,r.property⟩ : RegularTuning)
  have hsol : ProgramSolution (Geometry.shiftedCurve r.val.val (Threshold.sigma r.val.val)) nonzeroLags w := by
    rw [(mem_frontier_iff_sigma_zero r.val.val).mp r.val.property,Geometry.shiftedCurve_zero]
    exact hw
  have hcar := R.program_carried (fun n hn=>R.lags_nonzero n hn) hsol
  have hS : Set.range R.atoms=boundarySupport q := support_constant_on_plateau hr
  have hc : ∀ᵐω∂w,ω∈({frequencyZero}∪boundarySupport q : Set Frequency) := by
    filter_upwards [hcar] with ω hω
    rcases hω with rfl|⟨i,rfl⟩
    · exact Or.inl rfl
    · exact Or.inr (hS ▸ ⟨i,rfl⟩)
  apply unique_anchor_of_finite_carrier hgap hw
    ((finite_singleton frequencyZero).union (support_finite ⟨q.val.val,q.property⟩)) hc
  intro ω hω hωwin
  rcases hω with h0|hω
  · have heq : ω=frequencyZero := h0
    rw [heq] at hωwin
    have hlow := hωwin.1
    change 2*Real.pi/((K : ℝ)+1)<0 at hlow
    have hpos : 0<2*Real.pi/((K : ℝ)+1) := by positivity
    linarith
  · exact honly ω hω hωwin

end polyak.ModeLocking.Plateaus
