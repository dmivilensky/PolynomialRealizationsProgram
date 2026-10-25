import polyak.ModeLocking.Boundary.Classification
import polyak.ModeLocking.Boundary.Nonperiodic

/-! Dip mass, exclusion of finite rational carriers, and persistence of a fixed
finite carrier at limits of a plateau. -/
noncomputable section
namespace polyak.ModeLocking
open General Levels MeasureTheory Set Filter

theorem boundary_symbol_meets_dip {K:ℕ} {q:Tuning} (hq:q∈BoundaryInGap K)
    (S : Global.Symbols.LimitSymbol (tuningCurve q) nonzeroLags) :
    ∃ω:Frequency,S.weights.eval (tuningCurve q) ω=0 ∧ ω∈Geometry.closedDip (tuningCurve q) := by
  obtain ⟨w,hw⟩:=boundary_extremals_nonempty hq
  have hp:=Geometry.full_solution_closedDip_mass_pos hw
  have hcar:=S.carried w hw
  by_contra hn
  push Not at hn
  have hz : w {ω | S.weights.eval (tuningCurve q) ω≠0}=0 := by
    simpa only [ae_iff] using hcar
  have hsub : Geometry.closedDip (tuningCurve q)⊆{ω | S.weights.eval (tuningCurve q) ω≠0} := by
    intro ω hω he
    exact hn ω he hω
  exact hp.ne' (measure_mono_null hsub hz)

theorem finite_grid_carrier (F : Finset Frequency)
    (hF : ∀ω∈F,∃k:ℕ,3≤k ∧ ω∈periodicGrid k) :
    ∃L:ℕ,3≤L ∧ ∀ω∈F,ω∈periodicGrid L := by
  classical
  induction F using Finset.induction_on with
  | empty => exact ⟨3,le_rfl,by simp⟩
  | @insert x F hx ih =>
    obtain ⟨k,hk,hxk⟩:=hF x (Finset.mem_insert_self _ _)
    obtain ⟨L,hL,hcar⟩:=ih (fun ω hω=>hF ω (Finset.mem_insert_of_mem hω))
    refine ⟨k*L,by nlinarith,fun ω hω=>?_⟩
    rcases Finset.mem_insert.mp hω with rfl|hω
    · exact periodicGrid_mono_dvd ⟨L,rfl⟩ hxk
    · exact periodicGrid_mono_dvd ⟨k,Nat.mul_comm _ _⟩ (hcar ω hω)

theorem nonperiodic_no_finite_grid_carrier {K:ℕ} {q:Tuning}
    (hq:q∈BoundaryInGap K) (hn:¬PeriodicBoundary q)
    {w:Measure Frequency} (hw:Extremal q w) (F:Finset Frequency)
    (hF:∀ω∈F,∃k:ℕ,3≤k ∧ ω∈periodicGrid k) :
    ¬∀ᵐω∂w,ω∈(F:Set Frequency) := by
  intro hcar
  obtain ⟨L,hL,hFL⟩:=finite_grid_carrier F hF
  exact hn ((boundary_periodic_iff hq).mpr
    ⟨L,hL,w,(boundary_extremal_iff hq w).mp hw,hcar.mono (fun ω hω=>hFL ω hω)⟩)

theorem thresholdCurve_jointContinuous :
    Continuous (fun p:Tuning×Frequency=>Geometry.shiftedCurve p.1 (Threshold.sigma p.1) p.2) := by
  change Continuous (fun p:Tuning×Frequency => Geometry.shiftedAngle p.1 (Threshold.sigma p.1) p.2)
  have hs : Continuous (Threshold.sigma : Tuning→ℝ) := Global.Threshold.continuous_sigma
  have hp : Continuous (fun p:Tuning×Frequency => (p.1,Threshold.sigma p.1,p.2)) :=
    continuous_fst.prodMk ((hs.comp continuous_fst).prodMk continuous_snd)
  have hc := Geometry.shiftedAngle_jointContinuous.comp hp
  exact hc

theorem isClosed_threshold_supported {A:Set Frequency} (hA:IsClosed A) (hne:A.Nonempty) :
    IsClosed {q:Tuning | ∃ν:ProbabilityMeasure Frequency,
      ProbabilitySolution (Geometry.shiftedCurve q (Threshold.sigma q)) nonzeroLags ν ∧
        ∀ᵐω∂(ν:Measure Frequency),ω∈A} :=
  Threshold.isClosed_supported_family
    (fun q:Tuning=>Geometry.shiftedCurve q (Threshold.sigma q)) thresholdCurve_jointContinuous
      nonzeroLags hA hne

theorem closure_fixed_support {Aset:Set Tuning} {A:Set Frequency}
    (hA:IsClosed A) (hne:A.Nonempty)
    (hAset:∀q∈Aset,∃w:Measure Frequency,Extremal q w ∧ ∀ᵐω∂w,ω∈A)
    {q:Tuning} (hq:q∈closure Aset) :
    ∃ν:ProbabilityMeasure Frequency,
      ProbabilitySolution (Geometry.shiftedCurve q (Threshold.sigma q)) nonzeroLags ν ∧
        ∀ᵐω∂(ν:Measure Frequency),ω∈A := by
  apply (closure_minimal (fun p hp=>?_) (isClosed_threshold_supported hA hne)) hq
  obtain ⟨w,hw,hcar⟩:=hAset p hp
  exact hw.normalize_carried hcar

theorem closure_plateau_periodic {K L:ℕ} {Aset:Set Tuning} {F:Finset Frequency}
    (hL:3≤L) (hF:F.Nonempty) (hgrid:(F:Set Frequency)⊆periodicGrid L)
    (hAset:∀q∈Aset,∃w:Measure Frequency,Extremal q w ∧ ∀ᵐω∂w,ω∈(F:Set Frequency))
    {q:Tuning} (hq:q∈closure Aset) (hbd:q∈BoundaryInGap K) :
    Threshold.sigmaPeriodic q L=0 ∧
      ∃ν:ProbabilityMeasure Frequency,ProbabilitySolution (tuningCurve q) nonzeroLags ν ∧
        ∀ᵐω∂(ν:Measure Frequency),ω∈(F:Set Frequency) := by
  obtain ⟨ν,hν,hcar⟩:=closure_fixed_support F.finite_toSet.isClosed hF hAset hq
  rw [boundary_sigma_zero hbd,Geometry.shiftedCurve_zero] at hν
  have hp:PeriodicFP (tuningCurve q) L:=
    ⟨ν,hν.toProgramSolution,hcar.mono (fun _ h=>hgrid h)⟩
  refine ⟨le_antisymm ?_ ?_,ν,hν,hcar⟩
  · exact (Threshold.shifted_periodic_iff q hL 0).mp (by
      simpa only [Geometry.shiftedCurve_zero] using hp)
  · simpa only [boundary_sigma_zero hbd] using Threshold.sigma_le_sigmaPeriodic q hL

end polyak.ModeLocking
