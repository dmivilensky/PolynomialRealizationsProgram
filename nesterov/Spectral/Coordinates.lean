import nesterov.Spectral.Feasibility

/-! Exact probability-measure coordinates between the article's [0,π]
frequency interval and the cosine carrier used throughout the repository. -/
noncomputable section
open MeasureTheory
namespace nesterov.Spectral

abbrev Angle := polyak.Spectral.Angle
abbrev cosineCoordinates := polyak.Spectral.cosineCoordinates
abbrev spectrumCoordinates := polyak.Spectral.spectrumCoordinates

theorem meanG_spectrumCoordinates (ν : ProbabilityMeasure Angle) (a : SymbolPair) :
    meanG (spectrumCoordinates ν) a = ∫ ω,g a (cosineCoordinates ω) ∂ν :=
  polyak.Spectral.avg_spectrumCoordinates ν (continuous_g a)

theorem meanA_spectrumCoordinates (ν : ProbabilityMeasure Angle) (a : SymbolPair) (t : ℝ) (n : ℕ) :
    meanA (spectrumCoordinates ν) a t n = ∫ ω,lagA a t n (cosineCoordinates ω) ∂ν :=
  polyak.Spectral.avg_spectrumCoordinates ν (continuous_lagA a t n)

theorem meanB_spectrumCoordinates (ν : ProbabilityMeasure Angle) (a : SymbolPair) (n : ℕ) :
    meanB (spectrumCoordinates ν) a n = ∫ ω,lagB a n (cosineCoordinates ω) ∂ν :=
  polyak.Spectral.avg_spectrumCoordinates ν (continuous_lagB a n)

/-- All article spectra, including nonatomic ones and both frequency endpoints,
are represented exactly in the cosine-coordinate program. -/
theorem spectrumCoordinates_surjective (ν : Spectrum) :
    ∃ μ : ProbabilityMeasure Angle,spectrumCoordinates μ=ν :=
  polyak.Spectral.spectrumCoordinates_surjective ν

end nesterov.Spectral
