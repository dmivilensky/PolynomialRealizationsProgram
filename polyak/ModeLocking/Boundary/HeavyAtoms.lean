import polyak.ModeLocking.Boundary.HeavyPeriodic

/-! The full heavy-atoms proposition, with one common lower mass bound for
all normalized extremals, and with the literal finite-measure normalization. -/
noncomputable section
namespace polyak.ModeLocking
open General Levels MeasureTheory Set

def NormalizedExtremalMeasure (q:Tuning) (w:Measure Frequency) : Prop :=
  ProgramSolution (tuningCurve q) nonzeroLags w ∧ w {frequencyZero}=0 ∧
    w {ω:Frequency|0<(ω:ℝ)}=1

theorem positive_frequencies_eq_zero_compl :
    {ω:Frequency|0<(ω:ℝ)}=({frequencyZero}:Set Frequency)ᶜ := by
  ext ω
  change 0<(ω:ℝ) ↔ ω≠frequencyZero
  constructor
  · intro h he
    simp only [he,frequencyZero,lt_self_iff_false] at h
  · intro h
    exact lt_of_le_of_ne ω.property.1 (fun he=>h (Subtype.ext he.symm))

theorem normalized_extremal_measure_iff (q:Tuning) (w:Measure Frequency) :
    NormalizedExtremalMeasure q w ↔
      ∃ν:ProbabilityMeasure Frequency,NormalizedExtremal q ν ∧ (ν : Measure Frequency)=w := by
  constructor
  · rintro ⟨hw,hzero,hpos⟩
    rw [positive_frequencies_eq_zero_compl] at hpos
    have he:=measure_add_measure_compl (μ:=w) (measurableSet_singleton frequencyZero)
    rw [hzero,hpos,zero_add] at he
    let ν:ProbabilityMeasure Frequency:=⟨w,⟨he.symm⟩⟩
    exact ⟨ν,⟨⟨hw.2.2.1,hw.2.2.2⟩,hzero⟩,rfl⟩
  · rintro ⟨ν,hν,rfl⟩
    refine ⟨hν.1.toProgramSolution,hν.2,?_⟩
    rw [positive_frequencies_eq_zero_compl,
      measure_compl (measurableSet_singleton frequencyZero) (measure_ne_top _ _),hν.2]
    simp

theorem heavy_atoms_move_continuously {K:ℕ} {C:Set Tuning}
    (hC:C⊆BoundaryInGap K) (hconn:IsConnected C) {m:ℝ} (hm:1/2<m)
    (hh:∀q∈C,∀w:Measure Frequency,NormalizedExtremalMeasure q w→
      ∃x:Frequency,m≤w.real {x}) :
    ∃r:C→Frequency,
      (∀q:C,0<(r q:ℝ)) ∧
      (∀q:C,∀w:Measure Frequency,NormalizedExtremalMeasure q w→m≤w.real {r q}) ∧
      Continuous r ∧
      (∀q:C,PeriodicBoundary q→∃a:ℚ,(r q:ℝ)=2*Real.pi*(a:ℝ)) ∧
      ((¬∃x:Frequency,∀q:C,r q=x)→¬(C\{q|PeriodicBoundary q}).Countable) := by
  have hhp:∀q∈C,∀ν:ProbabilityMeasure Frequency,NormalizedExtremal q ν→
      ∃x:Frequency,m≤(ν : Measure Frequency).real {x}:=by
    intro q hq ν hν
    exact hh q hq ν ((normalized_extremal_measure_iff q ν).mpr ⟨ν,hν,rfl⟩)
  have hex:∀q:C,∃x:Frequency,0<(x:ℝ) ∧
      ∀ν:ProbabilityMeasure Frequency,NormalizedExtremal q ν→m≤(ν : Measure Frequency).real {x}:=
    fun q=>heavy_position_exists (hC q.property) hm (hhp q q.property)
  choose r hpos hr using hex
  refine ⟨r,hpos,?_,continuous_heavy_position hC hm hhp r hr,?_,
    nonconstant_heavy_uncountable hC hconn hm hhp r hr⟩
  · intro q w hw
    obtain ⟨ν,hν,rfl⟩:=(normalized_extremal_measure_iff q w).mp hw
    exact hr q ν hν
  · intro q hp
    exact periodic_heavy_angle_rational (hC q.property) hp hm (hr q)

end polyak.ModeLocking
