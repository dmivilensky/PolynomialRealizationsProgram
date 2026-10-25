import polyak.ModeLocking.Plateaus.Persistence

/-! Tight classes are intrinsic properties of all actual extremals.
Primary R1 identifies them exactly, so continuation preserves them. -/
noncomputable section
namespace polyak.ModeLocking.Plateaus
open General Levels Set MeasureTheory Filter
open scoped Topology

def TightLagAt (q : Tuning) (s : ℝ) (n : ℤ) : Prop :=
  ∀w : Measure Frequency,ProgramSolution (Geometry.shiftedCurve q s) nonzeroLags w→
    (∫ω,(Geometry.shiftedCurve q s).lag n ω∂w)=0

theorem integral_eq_of_mod {q : Tuning} {s : ℝ} {L : ℕ} (D : RegularData q s L)
    {w : Measure Frequency} (hw : ProgramSolution (Geometry.shiftedCurve q s) nonzeroLags w)
    {n m : ℤ} (hmod : n%(L : ℤ)=m%(L : ℤ)) :
    (∫ω,(Geometry.shiftedCurve q s).lag n ω∂w)=(∫ω,(Geometry.shiftedCurve q s).lag m ω∂w) := by
  apply integral_congr_ae
  filter_upwards [D.program_carried (N':=nonzeroLags) (fun n hn=>D.lags_nonzero n hn) hw] with ω hω
  rcases hω with rfl|⟨i,rfl⟩
  · simp only [Curve.lag_at_zero]
  · rw [lag_mod_grid _ (D.atoms_grid i) n,lag_mod_grid _ (D.atoms_grid i) m,hmod]

theorem tightLagAt_iff {q : Tuning} {s : ℝ} {L : ℕ} (D : RegularData q s L) (n : ℤ) :
    TightLagAt q s n ↔ n%(L : ℤ)=0 ∨ n%(L : ℤ)∈Set.range D.reps := by
  constructor
  · intro hn
    by_contra hnot
    have hz : n%(L : ℤ)≠0 := fun h=>hnot (Or.inl h)
    have hnone : ∀i,n%(L : ℤ)≠D.reps i := by
      intro i heq
      exact hnot (Or.inr ⟨i,heq.symm⟩)
    have hL : (0 : ℤ)<L := by have hL:=D.period_ge;omega
    have hr0 : 0<n%(L : ℤ) := lt_of_le_of_ne (Int.emod_nonneg n hL.ne') (Ne.symm hz)
    have hrL := Int.emod_lt_of_pos n hL
    have hp := D.inactive (n%(L : ℤ)) hr0 hrL hnone
    have he := hn D.measure D.primal_feasible
    rw [integral_eq_of_mod D D.primal_feasible (n:=n) (m:=n%(L : ℤ)) (by simp)] at he
    rw [RegularData.measure,atomicMeasure_integral] at he
    linarith
  · rintro (hz|⟨i,hi⟩) w hw
    · rw [integral_eq_of_mod D hw (n:=n) (m:=0) (by simpa using hz)]
      simp only [Curve.lag_zero,integral_zero]
    · obtain ⟨m,hm,_,_,_,hmclass,_⟩ := D.class_pair i
      rw [integral_eq_of_mod D hw (n:=n) (m:=m) (by rw [← hi,hmclass])]
      exact D.program_tight (N':=nonzeroLags) (fun n hn=>D.lags_nonzero n hn) hw m hm

def tightLags (q : RegularTuning) : Set ℤ := {n | TightLagAt q.val (Threshold.sigma q.val) n}

def activeClasses (q : RegularTuning) : Set ℤ :=
  {r | 0<r ∧ r<(leastPeriod q : ℤ) ∧ r∈tightLags q}

theorem tightLags_isLocallyConstant : IsLocallyConstant tightLags := by
  apply (IsLocallyConstant.iff_eventually_eq tightLags).mpr
  intro q
  have hp := (chosenData q).regular_persistence
  have hsub := (continuous_subtype_val.continuousAt : ContinuousAt (Subtype.val : RegularTuning→Tuning) q).eventually hp
  filter_upwards [hsub] with q' hq'
  obtain ⟨D',_,hR,_⟩ := hq'
  ext n
  change TightLagAt q'.val (Threshold.sigma q'.val) n ↔ TightLagAt q.val (Threshold.sigma q.val) n
  rw [tightLagAt_iff D',tightLagAt_iff (chosenData q),hR]

theorem activeClasses_isLocallyConstant : IsLocallyConstant activeClasses :=
  (leastPeriod_isLocallyConstant.prodMk tightLags_isLocallyConstant).comp
    (fun p : ℕ×Set ℤ=>{r | 0<r ∧ r<(p.1 : ℤ) ∧ r∈p.2})

theorem activeClasses_eq {q : Tuning} (hq : q∈regularTunings) {L : ℕ}
    (D : RegularData q (Threshold.sigma q) L) : activeClasses ⟨q,hq⟩=Set.range D.reps := by
  ext r
  change (0<r ∧ r<(leastPeriod ⟨q,hq⟩ : ℤ) ∧ TightLagAt q (Threshold.sigma q) r) ↔ _
  rw [leastPeriod_eq hq D,tightLagAt_iff D]
  constructor
  · rintro ⟨hr,hL,hzero|hclass⟩
    · rw [Int.emod_eq_of_lt hr.le hL] at hzero
      exact (hr.ne' hzero).elim
    · rwa [Int.emod_eq_of_lt hr.le hL] at hclass
  · rintro ⟨i,rfl⟩
    refine ⟨D.reps_pos i,D.reps_lt i,Or.inr ?_⟩
    rw [Int.emod_eq_of_lt (D.reps_pos i).le (D.reps_lt i)]
    exact ⟨i,rfl⟩

def boundaryTightLags (q : regularBoundary) : Set ℤ :=
  tightLags ⟨q.val.val,q.property⟩

theorem boundaryTightLags_isLocallyConstant : IsLocallyConstant boundaryTightLags := by
  have hc : Continuous (fun q : regularBoundary=>(⟨q.val.val,q.property⟩ : RegularTuning)) :=
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  exact tightLags_isLocallyConstant.comp_continuous hc

theorem tightLags_constant_on_plateau {q r : regularBoundary} (hr : r.val∈plateau q.val) :
    boundaryTightLags r=boundaryTightLags q :=
  label_constant_on_component boundaryTightLags_isLocallyConstant q r hr

def boundaryActiveClasses (q : regularBoundary) : Set ℤ :=
  activeClasses ⟨q.val.val,q.property⟩

theorem boundaryActiveClasses_isLocallyConstant : IsLocallyConstant boundaryActiveClasses := by
  have hc : Continuous (fun q : regularBoundary=>(⟨q.val.val,q.property⟩ : RegularTuning)) :=
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  exact activeClasses_isLocallyConstant.comp_continuous hc

theorem activeClasses_constant_on_plateau {q r : regularBoundary} (hr : r.val∈plateau q.val) :
    boundaryActiveClasses r=boundaryActiveClasses q :=
  label_constant_on_component boundaryActiveClasses_isLocallyConstant q r hr

end polyak.ModeLocking.Plateaus
