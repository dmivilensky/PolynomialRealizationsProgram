import krylov.Strings.SpectralPrincipal
import krylov.Strings.OptimizerRegularMaximum

/-!
Article: `main_krylov`, `thm:value`, the half-gamma optimal principal measure.
Attach the actual constructed principal spectral measure to the same
optimizing string whose reward, shooting coordinate, initial density and
finite total mass were already proved. The reciprocal zero atom is now a
theorem about that actual spectral measure, with no spectral certificate
assumed as an extra hypothesis.
-/

namespace krylov.Strings.Spectral
noncomputable section
open Set Filter MeasureTheory
open scoped Topology

/-- The principal spectral conclusion holds for the very same actual unique
maximizing mass recorded by the full continuum theorem. -/
theorem actualRegularMaximum_half_principal {σ : ℝ → ℝ} {M : Mass} {φ v : ℝ → ℝ}
    (h : ActualRegularMaximum (1 / 2) σ M φ v) :
    ∃ hfinite : IsFiniteMeasure M.measure,
      IsProbabilityMeasure (@principalMeasure M hfinite) ∧
      @principalMeasure M hfinite (Iio 0) = 0 ∧
      @principalMeasure M hfinite {0} = ENNReal.ofReal (σ 1)⁻¹ := by
  have hmass := h.half_mass rfl
  let hfinite := finiteMass_of_cumulative_limit M hmass
  refine ⟨hfinite, inferInstance, principalMeasure_negative M, ?_⟩
  rw [principalMeasure_zero, real_totalMass_of_cumulative_limit M hmass]

/-- Actual attainment, universal uniqueness, regularity, qualitative shape
and the nonnegative probability principal spectral measure all refer to one
and the same half-gamma string. Its zero atom is the reciprocal initial
shooting mass, hence equals its proved initial physical mass density. -/
theorem exists_actual_half_principal_attainment :
    ∃ σ : ℝ → ℝ,
      (∀ r ≥ 1, AnalyticAt ℝ σ r ∧ krylov.ContinuumControl.FeedbackGraphAt (1 / 2) σ r) ∧
      ∃ M : Mass, ∃ φ v : ℝ → ℝ,
      ActualRegularMaximum (1 / 2) σ M φ v ∧
      ∃ hfinite : IsFiniteMeasure M.measure,
      IsProbabilityMeasure (@principalMeasure M hfinite) ∧
      @principalMeasure M hfinite (Iio 0) = 0 ∧
      @principalMeasure M hfinite {0} = ENNReal.ofReal (σ 1)⁻¹ := by
  obtain ⟨σ, hσ, M, φ, v, h⟩ := exists_actual_regular_maximum
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 1)
  exact ⟨σ, hσ, M, φ, v, h, actualRegularMaximum_half_principal h⟩

end
end krylov.Strings.Spectral
