import polyak.Levels.Program.ProbabilityWeighting
import polyak.Levels.Program.SpectralBridge

/-! The normalized spectral bijection and dependence only on the source quadratic Xi. -/
noncomputable section
open MeasureTheory
namespace polyak.Levels

theorem probabilitySolution_normalize_iff (Θ : Curve) (𝒩 : Set ℤ)
    (μ : FiniteMeasure Frequency) (hμ : μ≠0) :
    ProbabilitySolution Θ 𝒩 μ.normalize ↔ ProgramSolution Θ 𝒩 (μ:Measure Frequency) := by
  have hm : (0:ℝ)<μ.mass := by exact_mod_cast (pos_iff_ne_zero.mpr (μ.mass_nonzero_iff.mpr hμ))
  have hi (f:Frequency→ℝ) : (0≤∫ω,f ω ∂μ.normalize) ↔ (0≤∫ω,f ω ∂(μ:Measure Frequency)) := by
    rw [integral_finiteMeasure_normalize μ hμ]
    exact mul_nonneg_iff_of_pos_left (inv_pos.mpr hm)
  constructor
  · rintro ⟨hG,hL⟩
    have hne : (μ:Measure Frequency)≠0 := fun he => hμ (FiniteMeasure.toMeasure_injective he)
    exact ⟨inferInstance,hne,(hi _).mp hG,fun n hn => (hi _).mp (hL n hn)⟩
  · rintro ⟨_,_,hG,hL⟩
    exact ⟨(hi _).mpr hG,fun n hn => (hi _).mpr (hL n hn)⟩

theorem probabilityReweight_source_iff (q : General.Tuning) (ν : ProbabilityMeasure Frequency) :
    ProbabilitySolution (tuningCurve q) nonzeroLags (probabilityReweight (sourceDensity q) ν) ↔
      RawSpectrumSolution q (ν:Measure Frequency) := by
  rw [probabilityReweight,probabilitySolution_normalize_iff _ _ _
    (finiteReweight_ne_zero (sourceDensity q) (sourceDensity_pos q) ν.toFiniteMeasure_nonzero)]
  exact (rawSpectrumSolution_iff_reweight q ν).symm

def thresholdProbabilityEquiv (q : General.Tuning) :
    {ν : ProbabilityMeasure Frequency // RawSpectrumSolution q (ν:Measure Frequency)} ≃
      {w : ProbabilityMeasure Frequency // ProbabilitySolution (tuningCurve q) nonzeroLags w} where
  toFun ν := ⟨probabilityReweight (sourceDensity q) ν,(probabilityReweight_source_iff q ν).mpr ν.property⟩
  invFun w := ⟨(probabilityReweightEquiv (sourceDensity q) (sourceDensity_pos q)).symm w,by
    apply (probabilityReweight_source_iff q _).mp
    change ProbabilitySolution (tuningCurve q) nonzeroLags
      ((probabilityReweightEquiv (sourceDensity q) (sourceDensity_pos q))
        ((probabilityReweightEquiv (sourceDensity q) (sourceDensity_pos q)).symm w))
    rw [(probabilityReweightEquiv (sourceDensity q) (sourceDensity_pos q)).apply_symm_apply]
    exact w.property⟩
  left_inv ν := Subtype.ext (probabilityReweight_inverse _ _ ν)
  right_inv w := Subtype.ext ((probabilityReweightEquiv (sourceDensity q) (sourceDensity_pos q)).apply_symm_apply w)

def sourceSpectrumAngleEquiv (q : General.Tuning) :
    {ν : ProbabilityMeasure Frequency // RawSpectrumSolution q (ν:Measure Frequency)} ≃
      {ν : Spectral.Spectrum // Waves.MixtureFeasible ν (Waves.multiplierMap q.A q.B q.beta 0) 0 0} :=
  Spectral.spectrumCoordinates.toEquiv.subtypeEquiv (rawSpectrum_probability_iff q)

def thresholdSpectrumEquiv (q : General.Tuning) :
    {ν : Spectral.Spectrum // Waves.MixtureFeasible ν (Waves.multiplierMap q.A q.B q.beta 0) 0 0} ≃
      {w : ProbabilityMeasure Frequency // ProbabilitySolution (tuningCurve q) nonzeroLags w} :=
  (sourceSpectrumAngleEquiv q).symm.trans (thresholdProbabilityEquiv q)

theorem tuningCurve_eq_of_Xi_eq {q q' : General.Tuning}
    (h : ∀c∈Set.Icc (-1:ℝ) 1,q.Xi c=q'.Xi c) : tuningCurve q=tuningCurve q' := by
  apply Curve.ext
  intro ω
  change q.angle ω=q'.angle ω
  unfold General.Tuning.angle General.Tuning.angleRadius
  rw [h (Real.cos ω) ⟨Real.neg_one_le_cos _,Real.cos_le_one _⟩]

theorem fp_iff_of_Xi_eq {q q' : General.Tuning}
    (h : ∀c∈Set.Icc (-1:ℝ) 1,q.Xi c=q'.Xi c) : FP (tuningCurve q) ↔ FP (tuningCurve q') := by
  rw [tuningCurve_eq_of_Xi_eq h]

end polyak.Levels
