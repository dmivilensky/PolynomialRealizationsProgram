import polyak.ModeLocking.Plateaus.IntrinsicSupport
import polyak.ModeLocking.Plateaus.BoundaryGraph
import Mathlib.Topology.LocallyConstant.Basic

/-! Canonical regular tuning labels and the connected components defining
plateaus, in the actual source tuning and frontier topologies. -/
noncomputable section
namespace polyak.ModeLocking.Plateaus
open General Levels Set

def regularTunings : Set Tuning := {q | ∃L : ℕ,RegularPoint q (Threshold.sigma q) L}
abbrev RegularTuning := regularTunings

def chosenPeriod (q : RegularTuning) : ℕ := Classical.choose q.property

def chosenData (q : RegularTuning) : RegularData q.val (Threshold.sigma q.val) (chosenPeriod q) :=
  Classical.choice (Classical.choose_spec q.property)

/-- The positive support of the threshold extremal. -/
def support (q : RegularTuning) : Set Frequency := Set.range (chosenData q).atoms

theorem support_eq {q : Tuning} (hq : q∈regularTunings) {L : ℕ}
    (D : RegularData q (Threshold.sigma q) L) : support ⟨q,hq⟩=Set.range D.atoms :=
  regular_support_eq (chosenData ⟨q,hq⟩) D

theorem support_finite (q : RegularTuning) : (support q).Finite := Set.finite_range _

theorem support_nonempty (q : RegularTuning) : (support q).Nonempty := by
  have hd := (chosenData q).d_pos
  exact ⟨(chosenData q).atoms ⟨0,hd⟩,⟨⟨0,hd⟩,rfl⟩⟩

/-- The least grid period, defined from the intrinsic support alone. -/
def leastPeriod (q : RegularTuning) : ℕ := sInf {L : ℕ | 3≤L ∧ support q⊆periodicGrid L}

theorem support_periods_nonempty (q : RegularTuning) :
    {L : ℕ | 3≤L ∧ support q⊆periodicGrid L}.Nonempty := by
  refine ⟨chosenPeriod q,(chosenData q).period_ge,?_⟩
  rintro _ ⟨i,rfl⟩
  exact (chosenData q).atoms_grid i

abbrev BoundaryTuning := frontier Regions.divergenceSet

def regularBoundary : Set BoundaryTuning := {q | q.val∈regularTunings}

/-- A plateau is exactly the connected component of the relatively open
regular part of the actual divergence boundary. -/
def plateau (q : BoundaryTuning) : Set BoundaryTuning := connectedComponentIn regularBoundary q

def boundarySupport (q : regularBoundary) : Set Frequency :=
  support ⟨q.val.val,q.property⟩

def boundaryLeastPeriod (q : regularBoundary) : ℕ :=
  leastPeriod ⟨q.val.val,q.property⟩

end polyak.ModeLocking.Plateaus
