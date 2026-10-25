import polyak.Levels.Geometry.Windows
import polyak.Levels.Geometry.Gap
import polyak.Levels.Geometry.DipMass
import polyak.Levels.Lattice.Atoms
import polyak.Levels.Realization.ExactThreshold
import polyak.General.Regions.PhaseLocking

/-! The literal three alternatives of level zero, before their boundary refinements. -/
noncomputable section
namespace polyak.Levels.Geometry
open Set General MeasureTheory

theorem closedDip_empty_iff_omegaOne (q : Tuning) :
    closedDip (tuningCurve q)=∅ ↔ Regions.OmegaOne q := by
  rw [Regions.omegaOne_iff_angle]
  constructor
  · intro he ω hω
    have hn : (⟨ω,hω.1.le,hω.2⟩:Frequency)∉closedDip (tuningCurve q):=by rw [he]; simp
    exact lt_of_not_ge hn
  · intro h
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro ω hω
    have hi:=closedDip_interior_frequency (tuningCurve q) hω
    exact (not_le_of_gt (h ω ⟨hi.1,hi.2.le⟩)) hω

theorem levelZero_empty_converges (q : Tuning) (h : closedDip (tuningCurve q)=∅) :
    Regions.OmegaOne q ∧ q.rate<1 := by
  have hΩ:=(closedDip_empty_iff_omegaOne q).mp h
  refine ⟨hΩ,?_⟩
  apply (rate_lt_one_iff_infeasible q).mpr
  rintro ⟨w,hw⟩
  have hmass:=full_solution_closedDip_mass_pos hw
  rw [h,measure_empty] at hmass
  exact lt_irrefl _ hmass

theorem levelZero_grid_atom (q : Tuning) {K : ℕ} (hK : 3≤K)
    (h : firstFrequency K (by omega)∈closedDip (tuningCurve q)) :
    q.angle (2*Real.pi/K)≤Real.pi/K ∧
      ProgramSolution (tuningCurve q) nonzeroLags
        (MeasureTheory.Measure.dirac (firstFrequency K (by omega))) ∧ 1≤q.rate := by
  have hphase : q.angle (2*Real.pi/K)≤Real.pi/K := by
    change q.angle (2*Real.pi/K)≤(2*Real.pi/K)/2 at h
    convert h using 1
    ring
  have hsol:= (Lattice.rational_atom_program_iff (tuningCurve q)
    (j:=1) (k:=K) (by simp) (by omega) (firstFrequency K (by omega)) (by simp [firstFrequency])).mpr hphase
  exact ⟨hphase,hsol,fp_one_le_rate q ⟨_,hsol⟩⟩

/-- The trichotomy includes unique gap indices, all endpoints, and every
admissible tuning; no finite-spectrum hypothesis appears. -/
theorem levelZero_geometric_trichotomy (q : Tuning) :
    (closedDip (tuningCurve q)=∅) ∨
    (∃K : ℕ,∃hK : 3≤K,firstFrequency K (by omega)∈closedDip (tuningCurve q)) ∨
    (closedDip (tuningCurve q)).Nonempty ∧
      ∃!K : ℕ,2≤K ∧ ∀ω∈closedDip (tuningCurve q),InWindow K ω := by
  classical
  by_cases he : closedDip (tuningCurve q)=∅
  · exact Or.inl he
  · right
    by_cases hg : ∃K : ℕ,∃hK : 3≤K,firstFrequency K (by omega)∈closedDip (tuningCurve q)
    · exact Or.inl hg
    · right
      have hne : (closedDip (tuningCurve q)).Nonempty:=Set.nonempty_iff_ne_empty.mpr he
      refine ⟨hne,interval_unique_window ?_ hne (fun ω hω=>closedDip_interior_frequency _ hω) ?_⟩
      · simpa only [shiftedCurve_zero] using closedDip_ordConnected q 0
      · intro K hK hm
        exact hg ⟨K,hK,hm⟩

/-- The window condition implies both strict tongue-edge inequalities of
the original definition, including the exceptional upper endpoint K=2. -/
theorem gap_of_closedDip_window (q : Tuning) {K : ℕ} (hK : 2≤K)
    (hd : (dip (tuningCurve q)).Nonempty)
    (hw : ∀ω∈closedDip (tuningCurve q),InWindow K ω) : Gap K q := by
  refine ⟨hK,hd,fun ω hω=>hw ω (show (tuningCurve q) ω≤(ω:ℝ)/2 from le_of_lt hω),?_,?_⟩
  · have hn : firstFrequency K hK∉closedDip (tuningCurve q):=by
      intro hm
      exact lt_irrefl _ (hw _ hm).2
    have hh : (2*Real.pi/K)/2<q.angle (2*Real.pi/K):=lt_of_not_ge hn
    convert hh using 1
    ring
  · have hn : firstFrequency (K+1) (by omega)∉closedDip (tuningCurve q):=by
      intro hm
      have hh:=(hw _ hm).1
      change 2*Real.pi/((K:ℝ)+1)<2*Real.pi/((K+1:ℕ):ℝ) at hh
      simp only [Nat.cast_add,Nat.cast_one] at hh
      exact lt_irrefl _ hh
    have hh : (2*Real.pi/((K+1:ℕ):ℝ))/2<q.angle (2*Real.pi/((K+1:ℕ):ℝ)):=lt_of_not_ge hn
    simpa only [Nat.cast_add,Nat.cast_one,show (2*Real.pi/((K:ℝ)+1))/2=Real.pi/((K:ℝ)+1) by ring] using hh

end polyak.Levels.Geometry
