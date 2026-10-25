import polyak.Spectral.Feasibility

/-!
Article: waves use ω∈[0,π], while (abg) uses c=cos ω∈[-1,1].
Use: an exact change of coordinate for every probability measure, with its weak topology.
Proof: cosine and arccosine are inverse continuous maps, and push-forwards preserve their inverses.
Source: mathlib cosine/arccosine inverse identities and probability push-forward continuity.
-/

noncomputable section

open MeasureTheory

namespace polyak.Spectral

/-- Article: the original frequency interval. Use: direct comparison with the angle formulation. -/
abbrev Angle := Set.Icc (0 : ℝ) Real.pi

/-- Article: c=cos ω. Use: both endpoints are retained in the coordinate change. -/
def cosineCoordinates : Angle ≃ₜ Frequency where
  toFun ω := ⟨Real.cos ω, Real.neg_one_le_cos _, Real.cos_le_one _⟩
  invFun c := ⟨Real.arccos c, Real.arccos_nonneg _, Real.arccos_le_pi _⟩
  left_inv ω := Subtype.ext (Real.arccos_cos ω.property.1 ω.property.2)
  right_inv c := Subtype.ext (Real.cos_arccos c.property.1 c.property.2)
  continuous_toFun := (Real.continuous_cos.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (Real.continuous_arccos.comp continuous_subtype_val).subtype_mk _

/-- Article: passage from angle spectra to cosine spectra.
Use: the full space of probability measures, not just finite atomic measures.
Proof: inverse continuous push-forwards along the frequency homeomorphism. -/
def spectrumCoordinates : ProbabilityMeasure Angle ≃ₜ Spectrum where
  toFun ν := ν.map cosineCoordinates
  invFun ν := ν.map cosineCoordinates.symm
  left_inv ν := by
    apply Subtype.ext
    change Measure.map (cosineCoordinates.symm : Frequency → Angle)
      (Measure.map (cosineCoordinates : Angle → Frequency) (ν : Measure Angle)) = _
    rw [Measure.map_map cosineCoordinates.symm.measurable cosineCoordinates.measurable]
    have heq : (cosineCoordinates.symm : Frequency → Angle) ∘ cosineCoordinates = id := by
      funext ω
      exact cosineCoordinates.symm_apply_apply ω
    rw [heq, Measure.map_id]
    rfl
  right_inv ν := by
    apply Subtype.ext
    change Measure.map (cosineCoordinates : Angle → Frequency)
      (Measure.map (cosineCoordinates.symm : Frequency → Angle) (ν : Measure Frequency)) = _
    rw [Measure.map_map cosineCoordinates.measurable cosineCoordinates.symm.measurable]
    have heq : (cosineCoordinates : Angle → Frequency) ∘ cosineCoordinates.symm = id := by
      funext c
      exact cosineCoordinates.apply_symm_apply c
    rw [heq, Measure.map_id]
    rfl
  continuous_toFun := ProbabilityMeasure.continuous_map cosineCoordinates.continuous
  continuous_invFun := ProbabilityMeasure.continuous_map cosineCoordinates.symm.continuous

/-- Article: bars are unchanged by the cosine coordinate change.
Proof: the integral push-forward formula for continuous real integrands. -/
theorem avg_spectrumCoordinates (ν : ProbabilityMeasure Angle) {f : Frequency → ℝ}
    (hf : Continuous f) :
    avg (spectrumCoordinates ν) f = ∫ ω, f (cosineCoordinates ω) ∂ν := by
  exact integral_map cosineCoordinates.measurable.aemeasurable hf.aestronglyMeasurable

/-- Article: every cosine spectrum is a spectrum on the original angle interval.
Proof: the inverse probability-measure homeomorphism. -/
theorem spectrumCoordinates_surjective (ν : Spectrum) :
    ∃ μ : ProbabilityMeasure Angle, spectrumCoordinates μ = ν :=
  ⟨spectrumCoordinates.symm ν, spectrumCoordinates.apply_symm_apply ν⟩

end polyak.Spectral
