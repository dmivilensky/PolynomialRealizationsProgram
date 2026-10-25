import polyak.ModeLocking.Modelock.Results
import polyak.ModeLocking.Boundary.Frontier
import polyak.ModeLocking.Boundary.Classification

/-! The analytic zero graph is the actual divergence boundary, rather than
an unrelated root of the determinant or of the continued primal system. -/
noncomputable section
namespace polyak.ModeLocking.Gradient
open General

theorem continuous_planeParameters : Continuous planeParameters := by
  apply continuous_pi
  intro i
  fin_cases i
  · exact Tuning.continuous_y
  · exact Tuning.continuous_beta

theorem continuous_graphCoordinates :
    Continuous (fun q:Tuning=>(planeParameters q,q.kappa)) :=
  continuous_planeParameters.prodMk Tuning.continuous_kappa

end polyak.ModeLocking.Gradient

namespace polyak.ModeLocking.RegularData.ContinuationData
open General Levels _root_.polyak.ModeLocking.Gradient Filter Set
open scoped Topology
variable {q:Tuning} {s:ℝ} {L:ℕ} {D:RegularData q s L} (C:D.ContinuationData)

include C in
theorem analytic_boundary_graph (hs:s=0) :
    ∃g:Plane→ℝ,AnalyticAt ℝ g (planeParameters q) ∧ g (planeParameters q)=q.kappa ∧
      ∀ᶠq' in 𝓝 q,
        (q'∈frontier Regions.divergenceSet ↔g (planeParameters q')=q'.kappa) ∧
        ((Global.Threshold.kappaBoundary (Global.Threshold.parameters q')).val=(q'.kappa:EReal) ↔
          g (planeParameters q')=q'.kappa) := by
  obtain ⟨g,hg,hbase,_,hiff⟩:=C.analytic_shift_zero_graph hs
  have hqi:=continuous_graphCoordinates.continuousAt.eventually hiff
  refine ⟨g,hg,hbase,?_⟩
  filter_upwards [hqi,C.shift_eq_sigma] with q' hi he
  change C.shift (Continuation.parameters q')=0 ↔g (planeParameters q')=q'.kappa at hi
  rw [he] at hi
  exact ⟨(mem_frontier_iff_sigma_zero q').trans hi,(on_boundary_iff_sigma_zero q').trans hi⟩

end polyak.ModeLocking.RegularData.ContinuationData

namespace polyak.ModeLocking.RegularData
open General Levels _root_.polyak.ModeLocking.Gradient Filter Set
open scoped Topology
variable {q:Tuning} {s:ℝ} {L:ℕ} (D:RegularData q s L)

include D in
theorem analytic_divergence_boundary (hs:s=0) :
    ∃g:Plane→ℝ,AnalyticAt ℝ g (planeParameters q) ∧ g (planeParameters q)=q.kappa ∧
      ∃U:Set Tuning,IsOpen U ∧ q∈U ∧ ∀q'∈U,
        q'∈frontier Regions.divergenceSet ↔g (planeParameters q')=q'.kappa := by
  obtain ⟨C⟩:=D.continuationData_nonempty
  obtain ⟨g,hg,hbase,hiff⟩:=C.analytic_boundary_graph hs
  have hh:∀ᶠq' in 𝓝 q,q'∈frontier Regions.divergenceSet ↔g (planeParameters q')=q'.kappa:=
    hiff.mono fun _ h=>h.1
  obtain ⟨U,hU,ho,hq⟩:=mem_nhds_iff.mp hh
  exact ⟨g,hg,hbase,U,ho,hq,fun q' hq'=>hU hq'⟩

end polyak.ModeLocking.RegularData
