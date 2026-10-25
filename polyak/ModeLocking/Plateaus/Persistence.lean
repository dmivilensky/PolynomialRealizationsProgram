import polyak.ModeLocking.Plateaus.Components
import polyak.ModeLocking.Plateaus.Periods
import polyak.ModeLocking.Regular.Persistence

/-! Openness and constancy on the actual plateau components are derived
from the fully constructed continuation of all primary regular data. -/
noncomputable section
namespace polyak.ModeLocking.Plateaus
open General Levels Set Filter
open scoped Topology

theorem isOpen_regularTunings : IsOpen regularTunings := by
  apply isOpen_iff_mem_nhds.mpr
  intro q hq
  obtain ⟨L,⟨D⟩⟩ := hq
  filter_upwards [D.regular_persistence] with q' hq'
  obtain ⟨D',_,_,_⟩ := hq'
  exact ⟨L,⟨D'⟩⟩

theorem support_isLocallyConstant : IsLocallyConstant support := by
  apply (IsLocallyConstant.iff_eventually_eq support).mpr
  intro q
  have hp := (chosenData q).regular_persistence
  have hsub := (continuous_subtype_val.continuousAt : ContinuousAt (Subtype.val : RegularTuning→Tuning) q).eventually hp
  filter_upwards [hsub] with q' hq'
  obtain ⟨D',hS,_,_⟩ := hq'
  rw [support_eq q'.property D',hS]
  rfl

theorem leastPeriod_isLocallyConstant : IsLocallyConstant leastPeriod :=
  support_isLocallyConstant.comp (fun S : Set Frequency=>sInf {L : ℕ | 3≤L ∧ S⊆periodicGrid L})

theorem isOpen_regularBoundary : IsOpen regularBoundary :=
  isOpen_regularTunings.preimage continuous_subtype_val

theorem boundarySupport_isLocallyConstant : IsLocallyConstant boundarySupport := by
  have hc : Continuous (fun q : regularBoundary=>(⟨q.val.val,q.property⟩ : RegularTuning)) :=
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  exact support_isLocallyConstant.comp_continuous hc

theorem boundaryLeastPeriod_isLocallyConstant : IsLocallyConstant boundaryLeastPeriod := by
  have hc : Continuous (fun q : regularBoundary=>(⟨q.val.val,q.property⟩ : RegularTuning)) :=
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  exact leastPeriod_isLocallyConstant.comp_continuous hc

/-- Each plateau is relatively open in the actual divergence frontier. -/
theorem plateau_open (q : BoundaryTuning) : IsOpen (plateau q) :=
  component_open isOpen_regularBoundary q

theorem plateau_connected {q : BoundaryTuning} (hq : q∈regularBoundary) : IsConnected (plateau q) :=
  component_connected hq

/-- The positive support remains the same on the whole component. -/
theorem support_constant_on_plateau {q r : regularBoundary} (hr : r.val∈plateau q.val) :
    boundarySupport r=boundarySupport q :=
  label_constant_on_component boundarySupport_isLocallyConstant q r hr

theorem leastPeriod_constant_on_plateau {q r : regularBoundary} (hr : r.val∈plateau q.val) :
    boundaryLeastPeriod r=boundaryLeastPeriod q :=
  label_constant_on_component boundaryLeastPeriod_isLocallyConstant q r hr

end polyak.ModeLocking.Plateaus
