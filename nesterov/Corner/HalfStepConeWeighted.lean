import nesterov.Corner.HalfStepConeMeasure
import nesterov.Corner.HalfStepConeDictionary
import Mathlib.MeasureTheory.Measure.WithDensity

/-! The limiting sine cone is the cone of radial-weighted angular measures.
The weight is allowed to vanish; in particular neither an inverse density nor
a finite-epsilon realization of every limiting cone measure is asserted. -/
namespace nesterov.Corner
noncomputable section
open MeasureTheory Spectral

def halfStepWeight (ω : ConeAngle) : ℝ := 2*halfStepRadial ω

theorem continuous_halfStepWeight : Continuous halfStepWeight := by
  unfold halfStepWeight halfStepRadial
  fun_prop

theorem halfStepWeight_nonneg (ω : ConeAngle) : 0≤halfStepWeight ω :=
  mul_nonneg (by norm_num) (halfStepRadial_nonneg ω.property)

def halfStepWeighted (ν : Spectrum) : Measure ConeAngle :=
  ((ν:Measure Frequency).map polyak.Spectral.cosineCoordinates.symm).withDensity
    (fun ω=>ENNReal.ofReal (halfStepWeight ω))

instance halfStepWeighted_finite (ν : Spectrum) : IsFiniteMeasure (halfStepWeighted ν) := by
  have hi : Integrable halfStepWeight
      ((ν:Measure Frequency).map polyak.Spectral.cosineCoordinates.symm) :=
    continuous_halfStepWeight.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  apply isFiniteMeasure_withDensity
  rw [←ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ halfStepWeight_nonneg)]
  exact ENNReal.ofReal_ne_top

theorem integral_halfStepWeighted (ν : Spectrum) (f : ConeAngle→ℝ) (hf : Continuous f) :
    (∫ ω,f ω ∂halfStepWeighted ν)=
      ∫ c : Frequency,2*halfStepRadial (Real.arccos c)*f (polyak.Spectral.cosineCoordinates.symm c) ∂ν := by
  unfold halfStepWeighted
  rw [integral_withDensity_eq_integral_toReal_smul
    (μ := (ν:Measure Frequency).map polyak.Spectral.cosineCoordinates.symm)
    (f := fun ω=>ENNReal.ofReal (halfStepWeight ω))
    (ENNReal.measurable_ofReal.comp continuous_halfStepWeight.measurable)
    (ae_of_all _ fun _=>ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (halfStepWeight_nonneg _),smul_eq_mul]
  rw [integral_map (μ := (ν:Measure Frequency))
    (f := fun ω : ConeAngle=>halfStepWeight ω*f ω)
    polyak.Spectral.cosineCoordinates.symm.measurable.aemeasurable
    (continuous_halfStepWeight.mul hf).aestronglyMeasurable]
  rfl

theorem halfStepWeighted_upper (ν : Spectrum) (n : ℕ) :
    (∫ ω,halfStepUpper ω n ∂halfStepWeighted ν)=
      meanA ν halfStepLimitPair 0 n+meanB ν halfStepLimitPair n := by
  rw [integral_halfStepWeighted ν _ (continuous_halfStepUpper n)]
  have hiA := polyak.Spectral.integrable_continuous ν (continuous_lagA halfStepLimitPair 0 n)
  have hiB := polyak.Spectral.integrable_continuous ν (continuous_lagB halfStepLimitPair n)
  rw [meanA,meanB,←integral_add hiA hiB]
  apply integral_congr_ae
  exact ae_of_all _ fun c=>(halfStep_lag_upper n c).symm

theorem halfStepWeighted_lower (ν : Spectrum) (n : ℕ) :
    (∫ ω,halfStepLower ω n ∂halfStepWeighted ν)=
      meanA ν halfStepLimitPair 0 n-meanB ν halfStepLimitPair n := by
  rw [integral_halfStepWeighted ν _ (continuous_halfStepLower n)]
  have hiA := polyak.Spectral.integrable_continuous ν (continuous_lagA halfStepLimitPair 0 n)
  have hiB := polyak.Spectral.integrable_continuous ν (continuous_lagB halfStepLimitPair n)
  rw [meanA,meanB,←integral_sub hiA hiB]
  apply integral_congr_ae
  exact ae_of_all _ fun c=>(halfStep_lag_lower n c).symm

theorem halfStepLimitPair_meanG_nonneg (ν : Spectrum) : 0≤meanG ν halfStepLimitPair := by
  apply integral_nonneg
  intro c
  rw [halfStepLimitPair_g]
  positivity

theorem halfStep_feasible_iff (ν : Spectrum) (C : ℝ) :
    Feasible halfStepLimitPair 0 ν C ↔
      |C|≤meanG ν halfStepLimitPair ∧ HalfStepCone (halfStepWeighted ν) := by
  simp only [Feasible,mul_zero,Real.sinh_zero,mul_zero,add_zero,sub_zero]
  constructor
  · rintro ⟨hC,h⟩
    refine ⟨hC,fun n hn=>?_⟩
    rw [halfStepWeighted_upper,halfStepWeighted_lower]
    exact ⟨(h n hn).2,(h n hn).1⟩
  · rintro ⟨hC,h⟩
    refine ⟨hC,fun n hn=>?_⟩
    have hh := h n hn
    rw [halfStepWeighted_upper,halfStepWeighted_lower] at hh
    exact ⟨hh.2,hh.1⟩

theorem halfStep_exists_charge_iff (ν : Spectrum) :
    (∃ C : ℝ,Feasible halfStepLimitPair 0 ν C) ↔ HalfStepCone (halfStepWeighted ν) := by
  constructor
  · rintro ⟨C,hC⟩
    exact ((halfStep_feasible_iff ν C).mp hC).2
  · intro h
    exact ⟨0,(halfStep_feasible_iff ν 0).mpr ⟨by simpa using halfStepLimitPair_meanG_nonneg ν,h⟩⟩

end
end nesterov.Corner
