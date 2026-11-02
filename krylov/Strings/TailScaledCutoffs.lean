import krylov.Strings.TailScaledMeasure
import krylov.Strings.TailCutoffTests

/-!
Article: main_krylov, apC:prop:tauber, exact rescaling of the two tails.
Use: identify bounded compact cutoff integrals with the original truncated
moment and probability tail, before taking any limit.
Source: the actual weighted pushforward and elementary rational algebra.
-/

namespace krylov.Strings.Tail
noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal

/-- Set integrals of the actual compact rescaling are its defining
weighted spectral integrals over the exact preimage. -/
theorem setIntegral_scaledMeasure (ν : FiniteMeasure ℝ) (t : PositiveParameter)
    (h : C(UnitInterval, ℝ)) {E : Set UnitInterval} (hE : MeasurableSet E) :
    (∫ u in E, h u ∂scaledMeasure ν t) =
      ∫ ξ in compactPoint t ⁻¹' E, scaledWeight t ξ * h (compactPoint t ξ) ∂ν := by
  change (∫ u in E, h u ∂(((ν : Measure ℝ).withDensity
    (fun ξ ↦ ENNReal.ofReal (scaledWeight t ξ))).map (compactPoint t))) = _
  rw [setIntegral_map hE h.continuous.aestronglyMeasurable
    (compactPoint_continuous t).measurable.aemeasurable,
    restrict_withDensity (hE.preimage (compactPoint_continuous t).measurable),
    integral_withDensity_eq_integral_toReal_smul
      (scaledWeight_continuous t).measurable.ennreal_ofReal
      (Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (scaledWeight_bounds t _).1, smul_eq_mul]

/-- On the nonnegative spectral axis the compact moment cutoff means
exactly xi at most the scaling parameter. -/
theorem compactPoint_mem_moment_iff (t : PositiveParameter) {ξ : ℝ} (hξ : 0 ≤ ξ) :
    compactPoint t ξ ∈ momentSet ↔ ξ ≤ (t : ℝ) := by
  change (1 / 2 : ℝ) ≤ (t : ℝ) / (t + max ξ 0) ↔ _
  rw [max_eq_left hξ, le_div_iff₀ (add_pos_of_pos_of_nonneg t.property hξ)]
  constructor <;> intro h <;> linarith

/-- On the nonnegative spectral axis the compact tail cutoff means
exactly xi strictly above the scaling parameter. -/
theorem compactPoint_mem_tail_iff (t : PositiveParameter) {ξ : ℝ} (hξ : 0 ≤ ξ) :
    compactPoint t ξ ∈ tailSet ↔ (t : ℝ) < ξ := by
  change (t : ℝ) / (t + max ξ 0) < (1 / 2 : ℝ) ↔ _
  rw [max_eq_left hξ, div_lt_iff₀ (add_pos_of_pos_of_nonneg t.property hξ)]
  constructor <;> intro h <;> linarith

/-- The compact moment integral is the rescaled original first moment,
with the unit atom at zero automatically contributing zero. -/
theorem moment_integral_scaledMeasure (ν : FiniteMeasure ℝ)
    (hν : (ν : Measure ℝ) (Iio 0) = 0) (t : PositiveParameter) :
    (∫ u in momentSet, momentWeight u ∂scaledMeasure ν t) =
      (∫ ξ in Ioc 0 (t : ℝ), ξ ∂ν) / Real.sqrt (t : ℝ) := by
  rw [setIntegral_scaledMeasure ν t momentWeight momentSet_measurable,
    ← integral_indicator (momentSet_measurable.preimage (compactPoint_continuous t).measurable),
    ← integral_div, ← integral_indicator measurableSet_Ioc]
  apply integral_congr_ae
  filter_upwards [nonnegative_ae ν hν] with ξ hξ
  by_cases hx : ξ ≤ (t : ℝ)
  · have hm := (compactPoint_mem_moment_iff t hξ).mpr hx
    rw [indicator_of_mem (show ξ ∈ compactPoint t ⁻¹' momentSet from hm)]
    by_cases hz : ξ = 0
    · subst ξ
      simp [scaledWeight]
    · have hx0 : 0 < ξ := lt_of_le_of_ne hξ (Ne.symm hz)
      rw [indicator_of_mem (show ξ ∈ Ioc 0 (t : ℝ) from ⟨hx0, hx⟩)]
      have hm' : (1 / 2 : ℝ) ≤ (compactPoint t ξ : ℝ) := hm
      change scaledWeight t ξ * (1 / max (compactPoint t ξ : ℝ) (1 / 2)) = _
      rw [max_eq_left hm']
      change Real.sqrt (t : ℝ) * max ξ 0 / (max ξ 0 + t) *
        (1 / ((t : ℝ) / (t + max ξ 0))) = _
      rw [max_eq_left hξ]
      have hs := Real.sq_sqrt t.property.le
      have ht : (t : ℝ) ≠ 0 := (show (0 : ℝ) < t from t.property).ne'
      have hd : ξ + (t : ℝ) ≠ 0 := (add_pos_of_nonneg_of_pos hξ t.property).ne'
      have hdt : (t : ℝ) + ξ ≠ 0 := by simpa only [add_comm] using hd
      field_simp [ht, hd, hdt, (Real.sqrt_pos.mpr t.property).ne']
      nlinarith
  · have hm := (compactPoint_mem_moment_iff t hξ).not.mpr hx
    rw [indicator_of_notMem (show ξ ∉ compactPoint t ⁻¹' momentSet from hm),
      indicator_of_notMem (show ξ ∉ Ioc 0 (t : ℝ) from fun h ↦ hx h.2)]

/-- The compact tail integral is exactly the square-root-rescaled
original spectral tail. -/
theorem tail_integral_scaledMeasure (ν : FiniteMeasure ℝ)
    (hν : (ν : Measure ℝ) (Iio 0) = 0) (t : PositiveParameter) :
    (∫ u in tailSet, tailWeight u ∂scaledMeasure ν t) =
      Real.sqrt (t : ℝ) * (ν : Measure ℝ).real (Ioi (t : ℝ)) := by
  rw [setIntegral_scaledMeasure ν t tailWeight tailSet_measurable,
    ← integral_indicator (tailSet_measurable.preimage (compactPoint_continuous t).measurable)]
  have he : (∫ ξ, (compactPoint t ⁻¹' tailSet).indicator
      (fun ξ ↦ scaledWeight t ξ * tailWeight (compactPoint t ξ)) ξ ∂ν) =
      ∫ ξ in Ioi (t : ℝ), Real.sqrt (t : ℝ) ∂ν := by
    rw [← integral_indicator measurableSet_Ioi]
    apply integral_congr_ae
    filter_upwards [nonnegative_ae ν hν] with ξ hξ
    by_cases hx : (t : ℝ) < ξ
    · have hm := (compactPoint_mem_tail_iff t hξ).mpr hx
      rw [indicator_of_mem (show ξ ∈ compactPoint t ⁻¹' tailSet from hm),
        indicator_of_mem (show ξ ∈ Ioi (t : ℝ) from hx)]
      have hm' : (1 / 2 : ℝ) ≤ 1 - (compactPoint t ξ : ℝ) := by
        have hh : (compactPoint t ξ : ℝ) < 1 / 2 := hm
        linarith
      change scaledWeight t ξ * (1 / max (1 - (compactPoint t ξ : ℝ)) (1 / 2)) = _
      rw [max_eq_left hm']
      change Real.sqrt (t : ℝ) * max ξ 0 / (max ξ 0 + t) *
        (1 / (1 - (t : ℝ) / (t + max ξ 0))) = _
      rw [max_eq_left hξ]
      have hξ0 : ξ ≠ 0 := ne_of_gt (lt_trans t.property hx)
      have hd : ξ + (t : ℝ) ≠ 0 := (add_pos_of_nonneg_of_pos hξ t.property).ne'
      have hdt : (t : ℝ) + ξ ≠ 0 := by simpa only [add_comm] using hd
      field_simp [hd, hdt, hξ0]
      ring
    · have hm := (compactPoint_mem_tail_iff t hξ).not.mpr hx
      rw [indicator_of_notMem (show ξ ∉ compactPoint t ⁻¹' tailSet from hm),
        indicator_of_notMem (show ξ ∉ Ioi (t : ℝ) from hx)]
  rw [he, setIntegral_const, smul_eq_mul, mul_comm]

end
end krylov.Strings.Tail
