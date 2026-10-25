import polyak.Levels.Program.SpectralBridge

/-! Positive reweighting and probability normalization preserve every carried set. -/
noncomputable section
open MeasureTheory
namespace polyak.Levels

theorem finiteMeasure_normalize_carried (μ : FiniteMeasure Frequency) (hne : μ≠0)
    {S : Set Frequency} (hS : ∀ᵐω∂(μ:Measure Frequency),ω∈S) :
    ∀ᵐω∂(μ.normalize:Measure Frequency),ω∈S := by
  rw [μ.toMeasure_normalize_eq_of_nonzero hne]
  change ∀ᵐω∂(((μ.mass⁻¹:NNReal):ENNReal) • (μ:Measure Frequency)),ω∈S
  exact Measure.smul_absolutelyContinuous.ae_le hS

theorem finiteMeasure_normalize_mutually_ac (μ : FiniteMeasure Frequency) (hne : μ≠0) :
    (μ.normalize:Measure Frequency) ≪ (μ:Measure Frequency) ∧
      (μ:Measure Frequency) ≪ (μ.normalize:Measure Frequency) := by
  rw [μ.toMeasure_normalize_eq_of_nonzero hne]
  change (((μ.mass⁻¹:NNReal):ENNReal) • (μ:Measure Frequency)) ≪ (μ:Measure Frequency) ∧
    (μ:Measure Frequency) ≪ (((μ.mass⁻¹:NNReal):ENNReal) • (μ:Measure Frequency))
  refine ⟨Measure.smul_absolutelyContinuous,Measure.absolutelyContinuous_smul ?_⟩
  exact_mod_cast inv_ne_zero (μ.mass_nonzero_iff.mpr hne)

theorem ProgramSolution.normalize_carried {Θ : Curve} {𝒩 : Set ℤ} {w : Measure Frequency}
    (h : ProgramSolution Θ 𝒩 w) {S : Set Frequency} (hS : ∀ᵐω∂w,ω∈S) :
    ∃ν : ProbabilityMeasure Frequency,ProbabilitySolution Θ 𝒩 ν ∧
      ∀ᵐω∂(ν:Measure Frequency),ω∈S := by
  let wf : FiniteMeasure Frequency := ⟨w,h.1⟩
  have hw : wf≠0 := by intro he; exact h.2.1 (congrArg FiniteMeasure.toMeasure he)
  refine ⟨wf.normalize,⟨?_,fun n hn => ?_⟩,finiteMeasure_normalize_carried wf hw hS⟩
  · rw [integral_finiteMeasure_normalize wf hw]
    exact mul_nonneg (by positivity) h.2.2.1
  · rw [integral_finiteMeasure_normalize wf hw]
    exact mul_nonneg (by positivity) (h.2.2.2 n hn)

theorem RawSpectrumSolution.normalize_carried {q : General.Tuning} {μ : Measure Frequency}
    (h : RawSpectrumSolution q μ) {S : Set Frequency} (hS : ∀ᵐω∂μ,ω∈S) :
    ∃ν : ProbabilityMeasure Frequency, RawSpectrumSolution q ν ∧ ∀ᵐω∂(ν:Measure Frequency),ω∈S := by
  let mf : FiniteMeasure Frequency := ⟨μ,h.1⟩
  have hm : mf≠0 := by intro he; exact h.2.1 (congrArg FiniteMeasure.toMeasure he)
  refine ⟨mf.normalize,⟨inferInstance,IsProbabilityMeasure.ne_zero _,?_,?_⟩,
    finiteMeasure_normalize_carried mf hm hS⟩
  · rw [integral_finiteMeasure_normalize mf hm]
    exact mul_nonneg (by positivity) h.2.2.1
  · intro n hn
    rw [integral_finiteMeasure_normalize mf hm]
    exact mul_nonneg (by positivity) (h.2.2.2 n hn)

theorem ProgramSolution.source_probability_carried {q : General.Tuning} {w : Measure Frequency}
    (h : ProgramSolution (tuningCurve q) nonzeroLags w) {S : Set Frequency}
    (hS : ∀ᵐω∂w,ω∈S) :
    ∃ν : ProbabilityMeasure Frequency, RawSpectrumSolution q ν ∧ ∀ᵐω∂(ν:Measure Frequency),ω∈S := by
  let μ := (thresholdMeasureEquiv q).symm ⟨w,h⟩
  have hμS : ∀ᵐω∂(μ:Measure Frequency),ω∈S := by
    exact (withDensity_absolutelyContinuous w _).ae_le hS
  exact μ.property.normalize_carried hμS

theorem RawSpectrumSolution.normalize_mutually_ac {q : General.Tuning} {μ : Measure Frequency}
    (h : RawSpectrumSolution q μ) :
    ∃ν : ProbabilityMeasure Frequency, RawSpectrumSolution q ν ∧
      (ν:Measure Frequency) ≪ μ ∧ μ ≪ (ν:Measure Frequency) := by
  let mf : FiniteMeasure Frequency := ⟨μ,h.1⟩
  have hm : mf≠0 := by intro he; exact h.2.1 (congrArg FiniteMeasure.toMeasure he)
  refine ⟨mf.normalize,⟨inferInstance,IsProbabilityMeasure.ne_zero _,?_,?_⟩,
    (finiteMeasure_normalize_mutually_ac mf hm).1,(finiteMeasure_normalize_mutually_ac mf hm).2⟩
  · rw [integral_finiteMeasure_normalize mf hm]
    exact mul_nonneg (by positivity) h.2.2.1
  · intro n hn
    rw [integral_finiteMeasure_normalize mf hm]
    exact mul_nonneg (by positivity) (h.2.2.2 n hn)

theorem ProgramSolution.source_probability_mutually_ac {q : General.Tuning} {w : Measure Frequency}
    (h : ProgramSolution (tuningCurve q) nonzeroLags w) :
    ∃ν : ProbabilityMeasure Frequency, RawSpectrumSolution q ν ∧
      (ν:Measure Frequency) ≪ w ∧ w ≪ (ν:Measure Frequency) := by
  let μ := (thresholdMeasureEquiv q).symm ⟨w,h⟩
  have hμw : (μ:Measure Frequency) ≪ w := withDensity_absolutelyContinuous w _
  have hwμ : w ≪ (μ:Measure Frequency) := by
    have he : reweight (sourceDensity q) μ=w := reciprocal_reweight _ _ w
    rw [← he]
    exact withDensity_absolutelyContinuous _ _
  obtain ⟨ν,hν,hνμ,hμν⟩ := μ.property.normalize_mutually_ac
  exact ⟨ν,hν,hνμ.trans hμw,hwμ.trans hμν⟩

end polyak.Levels
