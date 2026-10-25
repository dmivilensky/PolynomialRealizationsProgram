import polyak.Levels.Program.Definitions

/-! Normalization preserves the complete measure program. -/
noncomputable section
open MeasureTheory
namespace polyak.Levels

instance : Nonempty Frequency := ⟨frequencyZero⟩

theorem integral_finiteMeasure_normalize (w : FiniteMeasure Frequency) (hw : w≠0)
    (f : Frequency → ℝ) :
    (∫ ω, f ω ∂w.normalize) = ((w.mass:ℝ)⁻¹)*(∫ ω, f ω ∂(w:Measure Frequency)) := by
  rw [w.toMeasure_normalize_eq_of_nonzero hw,integral_smul_nnreal_measure]
  change ((w.mass⁻¹ : NNReal) : ℝ)*(∫ ω,f ω ∂(w:Measure Frequency))=_
  rw [NNReal.coe_inv]

theorem ProgramSolution.normalize {Θ : Curve} {𝒩 : Set ℤ} {w : Measure Frequency}
    (h : ProgramSolution Θ 𝒩 w) :
    ∃ ν : ProbabilityMeasure Frequency, ProbabilitySolution Θ 𝒩 ν := by
  let wf : FiniteMeasure Frequency := ⟨w,h.1⟩
  have hwf : wf≠0 := by
    intro he
    apply h.2.1
    exact congrArg FiniteMeasure.toMeasure he
  refine ⟨wf.normalize,?_,fun n hn => ?_⟩
  · rw [integral_finiteMeasure_normalize wf hwf]
    exact mul_nonneg (inv_nonneg.mpr (NNReal.coe_nonneg _)) h.2.2.1
  · rw [integral_finiteMeasure_normalize wf hwf]
    exact mul_nonneg (inv_nonneg.mpr (NNReal.coe_nonneg _)) (h.2.2.2 n hn)

theorem fpOn_iff_probability (Θ : Curve) (𝒩 : Set ℤ) :
    FPOn Θ 𝒩 ↔ ∃ ν : ProbabilityMeasure Frequency, ProbabilitySolution Θ 𝒩 ν := by
  constructor
  · rintro ⟨w,hw⟩
    exact hw.normalize
  · rintro ⟨ν,hν⟩
    exact ⟨ν,hν.toProgramSolution⟩

theorem integrable_curve_lag (Θ : Curve) (n : ℤ) (w : Measure Frequency)
    [IsFiniteMeasure w] : Integrable (Θ.lag n) w :=
  (Θ.continuous_lag n).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem integrable_curve_minimizer (Θ : Curve) (w : Measure Frequency)
    [IsFiniteMeasure w] : Integrable Θ.minimizer w :=
  Θ.continuous_minimizer.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

end polyak.Levels
