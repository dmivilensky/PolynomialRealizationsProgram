import polyak.ModeLocking.Plateaus.TwoPoint
import polyak.ModeLocking.Plateaus.Projection
import polyak.ModeLocking.Plateaus.Anchors
import polyak.ModeLocking.Modelock.Boundary

/-! The exact point belongs to its actual open connected boundary plateau.
The original two-lag equation and its unique anchor hold on the whole
component, by intrinsic support and tightness, without a chart restriction. -/
noncomputable section
namespace polyak.ModeLocking.TwoLag.ExactData
open General Levels Geometry Set Filter MeasureTheory Plateaus
open scoped Topology
variable {q : Tuning} {K L : ℕ} (D : ExactData q 0 K L)

def boundaryPoint : regularBoundary :=
  ⟨⟨q,(mem_frontier_iff_sigma_zero q).mpr D.sigma_eq⟩,L,by
    change RegularPoint q (Threshold.sigma q) L
    rw [D.sigma_eq]
    exact D.regular⟩

theorem boundaryPoint_support : boundarySupport D.boundaryPoint=Set.range D.u := by
  obtain ⟨R,hS,_⟩ := D.exists_regularData
  have hex : ∃R' : RegularData q (Threshold.sigma q) L,Set.range R'.atoms=Set.range D.u := by
    rw [D.sigma_eq]
    exact ⟨R,hS⟩
  obtain ⟨R',hS'⟩ := hex
  exact (support_eq D.boundaryPoint.property R').trans hS'

/-- No ambient connectedness or numerical certificate is an input. -/
theorem lies_on_open_plateau :
    D.boundaryPoint.val∈plateau D.boundaryPoint.val ∧ IsOpen (plateau D.boundaryPoint.val) ∧
      IsConnected (plateau D.boundaryPoint.val) :=
  ⟨mem_connectedComponentIn D.boundaryPoint.property,plateau_open _,plateau_connected D.boundaryPoint.property⟩

theorem plateau_support {r : regularBoundary} (hr : r.val∈plateau D.boundaryPoint.val) :
    boundarySupport r=Set.range D.u :=
  (support_constant_on_plateau hr).trans D.boundaryPoint_support

theorem base_tight (n : ℤ) (hn : n∈pinLags K L) :
    n∈boundaryTightLags D.boundaryPoint := by
  obtain ⟨R,_,hN⟩ := D.exists_regularData
  intro w hw
  change ProgramSolution (Geometry.shiftedCurve q (Threshold.sigma q)) nonzeroLags w at hw
  change (∫ω,(Geometry.shiftedCurve q (Threshold.sigma q)).lag n ω∂w)=0
  rw [D.sigma_eq] at hw ⊢
  exact R.program_tight (fun m hm=>R.lags_nonzero m hm) hw n (hN ▸ hn)

theorem plateau_determinant_zero {r : regularBoundary}
    (hr : r.val∈plateau D.boundaryPoint.val) :
    (tuningCurve r.val.val).lag 1 (D.u 0)*(tuningCurve r.val.val).lag (-(K : ℤ)) (D.u 1)-
      (tuningCurve r.val.val).lag 1 (D.u 1)*(tuningCurve r.val.val).lag (-(K : ℤ)) (D.u 0)=0 := by
  let R := chosenData (⟨r.val.val,r.property⟩ : RegularTuning)
  have hS : Set.range R.atoms=Set.range D.u := D.plateau_support hr
  have ht := tightLags_constant_on_plateau hr
  have h₁ : (1 : ℤ)∈boundaryTightLags r := by
    rw [ht]
    exact D.base_tight 1 (by simp [pinLags])
  have h₂ : (-(K : ℤ))∈boundaryTightLags r := by
    rw [ht]
    exact D.base_tight (-(K : ℤ)) (by simp [pinLags])
  have he := two_point_tight_determinant R D.u D.u_injective hS h₁ h₂
  change (Geometry.shiftedCurve r.val.val (Threshold.sigma r.val.val)).lag 1 (D.u 0)*
    (Geometry.shiftedCurve r.val.val (Threshold.sigma r.val.val)).lag (-(K : ℤ)) (D.u 1)-
    (Geometry.shiftedCurve r.val.val (Threshold.sigma r.val.val)).lag 1 (D.u 1)*
    (Geometry.shiftedCurve r.val.val (Threshold.sigma r.val.val)).lag (-(K : ℤ)) (D.u 0)=0 at he
  rw [(mem_frontier_iff_sigma_zero r.val.val).mp r.val.property,Geometry.shiftedCurve_zero] at he
  exact he

/-- Analyticity is local at every point of the complete component, with the
fixed-frequency determinant equation valid everywhere on that component. -/
theorem plateau_analytic_graph {r : regularBoundary}
    (_hr : r.val∈plateau D.boundaryPoint.val) :
    ∃g:Gradient.Plane→ℝ,AnalyticAt ℝ g (Gradient.planeParameters r.val.val) ∧
      g (Gradient.planeParameters r.val.val)=r.val.val.kappa ∧
      ∃U:Set Tuning,IsOpen U ∧ r.val.val∈U ∧ ∀q'∈U,
        q'∈frontier Regions.divergenceSet ↔g (Gradient.planeParameters q')=q'.kappa := by
  exact (chosenData ⟨r.val.val,r.property⟩).analytic_divergence_boundary
    ((mem_frontier_iff_sigma_zero r.val.val).mp r.val.property)

/-- The function in the article is itself analytic on the entire open,
connected projected plateau, in the original two real parameters. -/
theorem plateau_analytic_boundary :
    IsOpen (projectedPlateau D.boundaryPoint.val) ∧
      IsConnected (projectedPlateau D.boundaryPoint.val) ∧
      AnalyticOnNhd ℝ ambientKappaBoundary (projectedPlateau D.boundaryPoint.val) :=
  ⟨projectedPlateau_open _,projectedPlateau_connected D.boundaryPoint.property,
    analyticOnNhd_ambientKappaBoundary_plateau _⟩

/-- Literal original-frequency determinant at every point of the actual
component, without asking the caller for a new regular certificate. -/
theorem plateau_determinant_at {r : BoundaryTuning}
    (hr : r∈plateau D.boundaryPoint.val) :
    (tuningCurve r.val).lag 1 (D.u 0)*(tuningCurve r.val).lag (-(K : ℤ)) (D.u 1)-
      (tuningCurve r.val).lag 1 (D.u 1)*(tuningCurve r.val).lag (-(K : ℤ)) (D.u 0)=0 :=
  D.plateau_determinant_zero (r:=⟨r,connectedComponentIn_subset regularBoundary _ hr⟩) hr

theorem plateau_unique_anchor (hbelow : (D.u 1 : ℝ)<2*Real.pi/((K : ℝ)+1))
    {r : regularBoundary} (hr : r.val∈plateau D.boundaryPoint.val) (hgap : Gap K r.val.val)
    {w : Measure Frequency} (hw : ProgramSolution (tuningCurve r.val.val) nonzeroLags w) :
    ∀ω : Frequency,Farey.Anchor r.val.val w ω ↔ω=D.u 0 := by
  let R := chosenData (⟨r.val.val,r.property⟩ : RegularTuning)
  have hsol : ProgramSolution (Geometry.shiftedCurve r.val.val (Threshold.sigma r.val.val)) nonzeroLags w := by
    rw [(mem_frontier_iff_sigma_zero r.val.val).mp r.val.property,Geometry.shiftedCurve_zero]
    exact hw
  have hcar := R.program_carried (fun n hn=>R.lags_nonzero n hn) hsol
  have hS : Set.range R.atoms=Set.range D.u := D.plateau_support hr
  have hc : ∀ᵐω∂w,ω∈({frequencyZero}∪Set.range D.u : Set Frequency) := by
    filter_upwards [hcar] with ω hω
    rcases hω with rfl|⟨i,rfl⟩
    · exact Or.inl rfl
    · exact Or.inr (hS ▸ ⟨i,rfl⟩)
  apply unique_anchor_of_finite_carrier hgap hw
    ((finite_singleton frequencyZero).union (finite_range D.u)) hc
  intro ω hω hωwin
  rcases hω with h0|⟨i,rfl⟩
  · have heq : ω=frequencyZero := h0
    rw [heq] at hωwin
    have hlow := hωwin.1
    change 2*Real.pi/((K : ℝ)+1)<0 at hlow
    have hpos : 0<2*Real.pi/((K : ℝ)+1) := by positivity
    linarith
  · fin_cases i
    · rfl
    · have hlow := hωwin.1
      change 2*Real.pi/((K : ℝ)+1)<(D.u 1 : ℝ) at hlow
      linarith

/-- Membership in the original gap boundary and the full projected
analytic plateau conclusion under precisely the additional source window
hypothesis of Corollary exactdD. -/
theorem exact_boundary_corollary (hwin : InWindow K (D.u 0)) :
    q∈BoundaryInGap K ∧ D.boundaryPoint.val∈plateau D.boundaryPoint.val ∧
      IsOpen (projectedPlateau D.boundaryPoint.val) ∧
      IsConnected (projectedPlateau D.boundaryPoint.val) ∧
      AnalyticOnNhd ℝ ambientKappaBoundary (projectedPlateau D.boundaryPoint.val) ∧
      ∀r∈plateau D.boundaryPoint.val,
        (tuningCurve r.val).lag 1 (D.u 0)*(tuningCurve r.val).lag (-(K : ℤ)) (D.u 1)-
          (tuningCurve r.val).lag 1 (D.u 1)*(tuningCurve r.val).lag (-(K : ℤ)) (D.u 0)=0 := by
  exact ⟨D.boundary_of_first_contact_window hwin,D.lies_on_open_plateau.1,
    D.plateau_analytic_boundary.1,D.plateau_analytic_boundary.2.1,
    D.plateau_analytic_boundary.2.2,fun _ hr=>D.plateau_determinant_at hr⟩

end polyak.ModeLocking.TwoLag.ExactData
