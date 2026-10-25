import polyak.ModeLocking.Boundary.Support
import Mathlib.MeasureTheory.Measure.Restrict

/-! Finite rational carriers, including endpoint atoms, are excluded at
nonperiodic boundary points. The remaining alternatives retain actual atoms
and a genuine nonzero atomless submeasure. -/
noncomputable section
namespace polyak.ModeLocking
open General Levels MeasureTheory Set Filter

def RationalFrequency (ω : Frequency) : Prop := ∃ r : ℚ, (r:ℝ)=(ω:ℝ)/(2*Real.pi)

theorem positive_rational_frequency_grid {ω : Frequency} (hω : 0<(ω:ℝ)) :
    RationalFrequency ω ↔ ∃ k : ℕ, 3≤k ∧ ω∈periodicGrid k := by
  constructor
  · rintro ⟨r,hr⟩
    refine ⟨3*r.den,by have hh := r.den_pos; omega,hω,(3:ℤ)*r.num,?_⟩
    rw [Rat.cast_def] at hr
    have hd : (r.den:ℝ)≠0 := by exact_mod_cast r.den_ne_zero
    have hpi : 2*Real.pi≠0 := by positivity
    have hh := (div_eq_div_iff hd hpi).mp hr
    push_cast
    nlinarith only [hh]
  · rintro ⟨k,hk,_hpos,j,hj⟩
    refine ⟨(j:ℚ)/k,?_⟩
    have hkpos : (0:ℝ)<k := by exact_mod_cast (show 0<k by omega)
    push_cast
    apply (div_eq_div_iff hkpos.ne' (by positivity : 2*Real.pi≠0)).mpr
    nlinarith only [hj]

/-- The finite carrier is allowed to contain the origin. Endpoint removal
preserves a nonzero feasible measure and therefore removes this obstruction. -/
theorem nonperiodic_no_finite_rational_carrier {K : ℕ} {q : Tuning}
    (hq : q∈BoundaryInGap K) (hn : ¬PeriodicBoundary q)
    {w : Measure Frequency} (hw : Extremal q w) (F : Finset Frequency)
    (hF : ∀ ω∈F, RationalFrequency ω) : ¬∀ᵐω∂w,ω∈(F:Set Frequency) := by
  classical
  intro hcar
  have hwp := (boundary_extremal_iff hq w).mp hw
  let u := w.restrict Threshold.interiorCarrier
  have hu : ProgramSolution (tuningCurve q) nonzeroLags u := hwp.remove_endpoints
  let A : Finset Frequency := F.filter (fun ω : Frequency => 0<(ω:ℝ))
  have hucar : ∀ᵐω∂u, ω∈(A:Set Frequency) := by
    filter_upwards [ae_restrict_of_ae hcar,
      ae_restrict_mem Threshold.measurableSet_interiorCarrier] with ω hω hωint
    exact Finset.mem_filter.mpr ⟨hω,hωint.1⟩
  have hA : ∀ ω∈A,∃k : ℕ,3≤k ∧ ω∈periodicGrid k := by
    intro ω hω
    have hh := Finset.mem_filter.mp hω
    exact (positive_rational_frequency_grid hh.2).mp (hF ω hh.1)
  exact nonperiodic_no_finite_grid_carrier hq hn ((boundary_extremal_iff hq u).mpr hu) A hA hucar

def HasNonatomicPart (w : Measure Frequency) : Prop :=
  ∃ v : Measure Frequency, v≠0 ∧ v≤w ∧ ∀ω : Frequency, v {ω}=0

/-- The three source alternatives for every extremal, with the last one
expressed by an actual nonzero atomless submeasure rather than terminology. -/
theorem nonperiodic_extremal_alternatives {K : ℕ} {q : Tuning}
    (hq : q∈BoundaryInGap K) (hn : ¬PeriodicBoundary q)
    {w : Measure Frequency} (hw : Extremal q w) :
    (∃ω : Frequency,0<w {ω} ∧ ¬RationalFrequency ω) ∨
      Set.Infinite {ω : Frequency | 0<w {ω}} ∨ HasNonatomicPart w := by
  classical
  by_cases hirr : ∃ω : Frequency,0<w {ω} ∧ ¬RationalFrequency ω
  · exact Or.inl hirr
  right
  let A : Set Frequency := {ω | 0<w {ω}}
  by_cases hA : A.Finite
  · right
    let v := w.restrict Aᶜ
    have hvne : v≠0 := by
      intro hz
      have hzA : w Aᶜ=0 := Measure.restrict_eq_zero.mp hz
      have hcar : ∀ᵐω∂w,ω∈A := by
        rw [ae_iff]
        exact hzA
      have hFA : ∀ω∈hA.toFinset,RationalFrequency ω := by
        intro ω hω
        have hp : 0<w {ω} := (Set.Finite.mem_toFinset hA).mp hω
        by_contra hh
        exact hirr ⟨ω,hp,hh⟩
      apply nonperiodic_no_finite_rational_carrier hq hn hw hA.toFinset hFA
      simpa only [Set.Finite.coe_toFinset] using hcar
    refine ⟨v,hvne,Measure.restrict_le_self,?_⟩
    intro ω
    change w.restrict Aᶜ {ω}=0
    rw [Measure.restrict_apply (measurableSet_singleton ω)]
    by_cases hω : ω∈A
    · have he : ({ω}:Set Frequency)∩Aᶜ=∅ := by
        ext x
        simp only [mem_inter_iff,mem_singleton_iff,mem_compl_iff,mem_empty_iff_false]
        exact ⟨fun h => h.2 (h.1 ▸ hω),False.elim⟩
      rw [he,measure_empty]
    · have hz : w {ω}=0 := le_antisymm (le_of_not_gt hω) bot_le
      exact measure_mono_null inter_subset_left hz
  · exact Or.inl hA

end polyak.ModeLocking
