import polyak.CertifiedExamples.Plateaus.Consequences
import polyak.ModeLocking.Plateaus.Source

/-! Concrete regular witnesses at shift zero yield the actual open boundary
plateau and its analytic graph. No numerical boundary identification is assumed. -/
noncomputable section
namespace polyak.CertifiedExamples.Plateaus
open General Levels ModeLocking ModeLocking.Plateaus Set MeasureTheory

def regularBoundaryPoint {q : Tuning} {L : ℕ} (D : RegularData q 0 L) : regularBoundary :=
  ⟨⟨q,(mem_frontier_iff_sigma_zero q).mpr D.sigma_eq⟩,L,by
    change RegularPoint q (Threshold.sigma q) L
    rw [D.sigma_eq]
    exact ⟨D⟩⟩

theorem regular_kappa_boundary {q : Tuning} {L : ℕ} (D : RegularData q 0 L) :
    (Global.Threshold.kappaBoundary (Global.Threshold.parameters q)).val=(q.kappa:EReal) := by
  apply (Global.Threshold.kappaBoundary_eq_iff (Global.Threshold.parameters q)
    (Global.Threshold.conditionNumber q)).mpr
  simpa only [Global.Threshold.fixedThreshold,Global.Threshold.tuning_parameters] using D.sigma_eq

theorem regularBoundaryPoint_support {q : Tuning} {L : ℕ} (D : RegularData q 0 L) :
    boundarySupport (regularBoundaryPoint D)=Set.range D.atoms := by
  have hex : ∃R : RegularData q (Threshold.sigma q) L,
      Set.range R.atoms=Set.range D.atoms := by
    rw [D.sigma_eq]
    exact ⟨D,rfl⟩
  obtain ⟨R,hR⟩ := hex
  exact (support_eq (regularBoundaryPoint D).property R).trans hR

theorem regular_open_plateau {q : Tuning} {L : ℕ} (D : RegularData q 0 L) :
    (regularBoundaryPoint D).val∈plateau (regularBoundaryPoint D).val ∧
      IsOpen (plateau (regularBoundaryPoint D).val) ∧
      IsConnected (plateau (regularBoundaryPoint D).val) :=
  ⟨mem_connectedComponentIn (regularBoundaryPoint D).property,plateau_open _,
    plateau_connected (regularBoundaryPoint D).property⟩

theorem regular_analytic_plateau {q : Tuning} {L : ℕ} (D : RegularData q 0 L) :
    IsOpen (projectedPlateau (regularBoundaryPoint D).val) ∧
      IsConnected (projectedPlateau (regularBoundaryPoint D).val) ∧
      AnalyticOnNhd ℝ ambientKappaBoundary (projectedPlateau (regularBoundaryPoint D).val) :=
  ⟨projectedPlateau_open _,projectedPlateau_connected (regularBoundaryPoint D).property,
    analyticOnNhd_ambientKappaBoundary_plateau _⟩

theorem regular_plateau_unique_anchor {q : Tuning} {L K : ℕ} (D : RegularData q 0 L)
    {star : Frequency}
    (honly : ∀ω∈Set.range D.atoms, Geometry.InWindow K ω→ω=star)
    {r : regularBoundary} (hr : r.val∈plateau (regularBoundaryPoint D).val)
    (hgap : Geometry.Gap K r.val.val) {w : Measure Frequency}
    (hw : ProgramSolution (tuningCurve r.val.val) nonzeroLags w) :
    ∀ω : Frequency,Farey.Anchor r.val.val w ω ↔ω=star := by
  apply plateau_unique_anchor hr hgap _ hw
  rw [regularBoundaryPoint_support]
  exact honly

end polyak.CertifiedExamples.Plateaus
