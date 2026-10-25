import polyak.ModeLocking.Boundary.AtomConvexity
import polyak.Levels.Program.SourceBijection
import polyak.Levels.Program.EndpointRemoval

/-! Removing a zero atom and normalizing preserves feasibility and can only
increase the mass of every other atom. -/
noncomputable section
namespace polyak.ModeLocking
open Levels General MeasureTheory Set

def NormalizedExtremal (q : Tuning) (ν : ProbabilityMeasure Frequency) : Prop :=
  ProbabilitySolution (tuningCurve q) nonzeroLags ν ∧
    (ν : Measure Frequency) {frequencyZero}=0

theorem normalize_away_zero {Θ : Curve} {N : Set ℤ} {ν : ProbabilityMeasure Frequency}
    (hν : ProbabilitySolution Θ N ν) :
    ∃ρ:ProbabilityMeasure Frequency,ProbabilitySolution Θ N ρ ∧
      (ρ : Measure Frequency) {frequencyZero}=0 ∧
      ∀x:Frequency,x≠frequencyZero→(ν : Measure Frequency).real {x}≤(ρ : Measure Frequency).real {x} := by
  let w := (ν : Measure Frequency).restrict ({frequencyZero} : Set Frequency)ᶜ
  have hw : ProgramSolution Θ N w := by
    apply hν.toProgramSolution.remove_bad (measurableSet_singleton frequencyZero)
    · intro ω hω
      rw [mem_singleton_iff] at hω
      rw [hω,Θ.minimizer_at_zero]
    · intro n _ ω hω
      rw [mem_singleton_iff] at hω
      rw [hω,Θ.lag_at_zero]
  let wf : FiniteMeasure Frequency := ⟨w,hw.1⟩
  have hwf : wf≠0 := by
    intro h
    exact hw.2.1 (congrArg FiniteMeasure.toMeasure h)
  have hmass : (wf.mass:ℝ)≤1 := by
    change w.real univ≤1
    change (((ν : Measure Frequency).restrict ({frequencyZero} : Set Frequency)ᶜ) univ).toReal≤1
    rw [Measure.restrict_apply_univ]
    exact (measureReal_mono (subset_univ _)).trans_eq (by simp)
  have hmasspos : 0<(wf.mass:ℝ) := by
    exact_mod_cast (pos_iff_ne_zero.mpr (wf.mass_nonzero_iff.mpr hwf))
  have hfac : 1≤(wf.mass:ℝ)⁻¹ := by
    have hi : 0≤(wf.mass:ℝ)⁻¹ := inv_nonneg.mpr hmasspos.le
    have he : (wf.mass:ℝ)*(wf.mass:ℝ)⁻¹=1 := mul_inv_cancel₀ hmasspos.ne'
    nlinarith
  refine ⟨wf.normalize,(probabilitySolution_normalize_iff Θ N wf hwf).mpr hw,?_,?_⟩
  · rw [wf.toMeasure_normalize_eq_of_nonzero hwf]
    change ((wf.mass⁻¹:NNReal) • w) {frequencyZero}=0
    simp [w,Measure.smul_apply,Measure.restrict_apply]
  · intro x hx
    rw [wf.toMeasure_normalize_eq_of_nonzero hwf,measureReal_nnreal_smul_apply]
    have hwx : w.real {x}=(ν : Measure Frequency).real {x} := by
      simp [w,Measure.real,Measure.restrict_apply,hx]
    change (ν : Measure Frequency).real {x}≤((wf.mass:ℝ)⁻¹)*w.real {x}
    rw [hwx]
    exact le_mul_of_one_le_left measureReal_nonneg hfac

theorem normalized_extremals_nonempty {K:ℕ} {q:Tuning} (hq:q∈BoundaryInGap K) :
    ∃ν:ProbabilityMeasure Frequency,NormalizedExtremal q ν := by
  obtain ⟨w,hw⟩:=boundary_extremals_nonempty hq
  obtain ⟨ν,hν⟩:=hw.normalize
  obtain ⟨ρ,hρ,hzero,_⟩:=normalize_away_zero hν
  exact ⟨ρ,hρ,hzero⟩

theorem normalized_extremal_mix {q:Tuning} {μ ν:ProbabilityMeasure Frequency}
    (hμ:NormalizedExtremal q μ) (hν:NormalizedExtremal q ν)
    {u v:ℝ} (hu:0≤u) (hv:0≤v) (huv:u+v=1) :
    NormalizedExtremal q (mixAngleMeasure μ ν u v hu hv huv) := by
  refine ⟨ProbabilitySolution.mix hμ.1 hν.1 hu hv huv,?_⟩
  have hr : (mixAngleMeasure μ ν u v hu hv huv : Measure Frequency).real {frequencyZero}=0 := by
    rw [mixAngleMeasure_real]
    simp only [Measure.real,hμ.2,hν.2,ENNReal.toReal_zero,mul_zero,add_zero]
  exact (measureReal_eq_zero_iff).mp hr

end polyak.ModeLocking
