import krylov.Strings.TailCauchy
import krylov.Strings.TailCutoffContinuity

/-!
Article: main_krylov, apC:prop:tauber, the two sharp cutoff constants.
Use: express the truncated first moment and the spectral tail through
bounded continuously weighted half-intervals of the compactified axis.
Source: elementary rational changes of variable in the actual half-Cauchy
limit; the unique cutoff fibre has zero mass.
-/

namespace krylov.Strings.Tail
noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal

/-- Compact half-interval corresponding to spectral energies at most t. -/
def momentSet : Set UnitInterval := {u | (1 / 2 : ℝ) ≤ u}

/-- Compact half-interval corresponding to spectral energies above t. -/
def tailSet : Set UnitInterval := {u | (u : ℝ) < 1 / 2}

/-- The truncated-moment cutoff is a Borel set. -/
theorem momentSet_measurable : MeasurableSet momentSet :=
  measurableSet_Ici.preimage measurable_subtype_coe

/-- The tail cutoff is a Borel set. -/
theorem tailSet_measurable : MeasurableSet tailSet :=
  measurableSet_Iio.preimage measurable_subtype_coe

/-- A bounded continuous extension of 1/u on the moment half-interval. -/
def momentWeight : C(UnitInterval, ℝ) :=
  ⟨fun u ↦ 1 / max (u : ℝ) (1 / 2), continuous_const.div (by fun_prop)
    (fun u ↦ ne_of_gt (lt_of_lt_of_le (by norm_num) (le_max_right (u : ℝ) (1 / 2))))⟩

/-- A bounded continuous extension of 1/(1-u) on the tail half-interval. -/
def tailWeight : C(UnitInterval, ℝ) :=
  ⟨fun u ↦ 1 / max (1 - (u : ℝ)) (1 / 2), continuous_const.div (by fun_prop)
    (fun u ↦ ne_of_gt (lt_of_lt_of_le (by norm_num) (le_max_right (1 - (u : ℝ)) (1 / 2))))⟩

/-- The moment cutoff weight is nonnegative everywhere. -/
theorem momentWeight_nonneg (u : UnitInterval) : 0 ≤ momentWeight u :=
  div_nonneg zero_le_one (le_trans (by norm_num) (le_max_right (u : ℝ) (1 / 2)))

/-- The tail cutoff weight is nonnegative everywhere. -/
theorem tailWeight_nonneg (u : UnitInterval) : 0 ≤ tailWeight u :=
  div_nonneg zero_le_one (le_trans (by norm_num) (le_max_right (1 - (u : ℝ)) (1 / 2)))

/-- The actual compact limit has zero mass on the cutoff fibre. -/
theorem arcsineMeasure_cutoff_null :
    (arcsineMeasure : Measure UnitInterval) {u | (u : ℝ) = 1 / 2} = 0 := by
  change (halfCauchy : Measure ℝ).map cauchyPoint {u | (u : ℝ) = 1 / 2} = 0
  have hE : MeasurableSet {u : UnitInterval | (u : ℝ) = 1 / 2} :=
    measurableSet_eq_fun measurable_subtype_coe measurable_const
  rw [Measure.map_apply cauchyPoint_continuous.measurable hE]
  apply measure_mono_null (t := ({-1, 1} : Set ℝ))
  · intro v hv
    change 1 / (1 + v ^ 2) = (1 / 2 : ℝ) at hv
    have hd : (1 : ℝ) + v ^ 2 ≠ 0 := by positivity
    have hs : v ^ 2 = 1 := by field_simp [hd] at hv; linarith
    have : v = -1 ∨ v = 1 := (sq_eq_one_iff.mp hs).symm
    simpa only [mem_insert_iff, mem_singleton_iff] using this
  · change ((volume.restrict (Ioi (0 : ℝ))).withDensity _) {-1, 1} = 0
    apply withDensity_absolutelyContinuous
    rw [Measure.restrict_apply (by measurability)]
    exact measure_mono_null (t := ({-1, 1} : Set ℝ)) inter_subset_left
      (((finite_singleton (1 : ℝ)).insert (-1)).measure_zero volume)

/-- The moment half-interval is a continuity set of the actual limit. -/
theorem arcsineMeasure_moment_frontier_null : arcsineMeasure (frontier momentSet) = 0 := by
  apply (FiniteMeasure.null_iff_toMeasure_null _ _).mpr
  apply measure_mono_null _ arcsineMeasure_cutoff_null
  intro u hu
  have hh := (continuous_subtype_val : Continuous (fun u : UnitInterval ↦ (u : ℝ))).frontier_preimage_subset (Ici (1 / 2 : ℝ)) hu
  change (u : ℝ) = 1 / 2
  simpa only [frontier_Ici, mem_preimage, mem_singleton_iff] using hh

/-- The tail half-interval is a continuity set of the actual limit. -/
theorem arcsineMeasure_tail_frontier_null : arcsineMeasure (frontier tailSet) = 0 := by
  apply (FiniteMeasure.null_iff_toMeasure_null _ _).mpr
  apply measure_mono_null _ arcsineMeasure_cutoff_null
  intro u hu
  have hh := (continuous_subtype_val : Continuous (fun u : UnitInterval ↦ (u : ℝ))).frontier_preimage_subset (Iio (1 / 2 : ℝ)) hu
  change (u : ℝ) = 1 / 2
  simpa only [frontier_Iio, mem_preimage, mem_singleton_iff] using hh

/-- Set integrals of the explicit compact limit are the actual
half-Cauchy integrals on the corresponding positive preimages. -/
theorem setIntegral_arcsineMeasure (h : C(UnitInterval, ℝ))
    {E : Set UnitInterval} (hE : MeasurableSet E) :
    (∫ u in E, h u ∂arcsineMeasure) =
      ∫ v in cauchyPoint ⁻¹' E ∩ Ioi 0, halfCauchyDensity v * h (cauchyPoint v) := by
  change (∫ u in E, h u ∂(halfCauchy : Measure ℝ).map cauchyPoint) = _
  rw [setIntegral_map hE h.continuous.aestronglyMeasurable
    cauchyPoint_continuous.measurable.aemeasurable]
  change (∫ v, h (cauchyPoint v) ∂((volume.restrict (Ioi (0 : ℝ))).withDensity
    (fun v ↦ ENNReal.ofReal (halfCauchyDensity v))).restrict (cauchyPoint ⁻¹' E)) = _
  rw [restrict_withDensity (hE.preimage cauchyPoint_continuous.measurable),
    Measure.restrict_restrict (hE.preimage cauchyPoint_continuous.measurable),
    integral_withDensity_eq_integral_toReal_smul
      halfCauchyDensity_continuous.measurable.ennreal_ofReal
      (Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (halfCauchyDensity_pos _).le, smul_eq_mul]

/-- The moment cutoff becomes the elementary interval (0,1] in the
half-Cauchy parametrization. -/
theorem cauchyPoint_preimage_moment : cauchyPoint ⁻¹' momentSet ∩ Ioi 0 = Ioc 0 1 := by
  ext v
  change ((1 / 2 : ℝ) ≤ 1 / (1 + v ^ 2) ∧ 0 < v) ↔ 0 < v ∧ v ≤ 1
  have hd : (0 : ℝ) < 1 + v ^ 2 := by positivity
  constructor
  · rintro ⟨h, hv⟩
    have hh := (le_div_iff₀ hd).mp h
    exact ⟨hv, by nlinarith [sq_nonneg (v - 1)]⟩
  · rintro ⟨hv, h1⟩
    exact ⟨(le_div_iff₀ hd).mpr (by nlinarith), hv⟩

/-- The tail cutoff becomes the elementary half-line (1,infinity). -/
theorem cauchyPoint_preimage_tail : cauchyPoint ⁻¹' tailSet ∩ Ioi 0 = Ioi 1 := by
  ext v
  change (1 / (1 + v ^ 2) < (1 / 2 : ℝ) ∧ 0 < v) ↔ 1 < v
  have hd : (0 : ℝ) < 1 + v ^ 2 := by positivity
  constructor
  · rintro ⟨h, hv⟩
    have hh := (div_lt_iff₀ hd).mp h
    nlinarith
  · intro hv
    exact ⟨(div_lt_iff₀ hd).mpr (by nlinarith [sq_nonneg (v - 1)]), by linarith⟩

/-- The first cutoff constant is exactly 2/pi. -/
theorem moment_integral_arcsineMeasure :
    (∫ u in momentSet, momentWeight u ∂arcsineMeasure) = 2 / Real.pi := by
  rw [setIntegral_arcsineMeasure momentWeight momentSet_measurable,
    cauchyPoint_preimage_moment]
  have he : (∫ v in Ioc (0 : ℝ) 1, halfCauchyDensity v * momentWeight (cauchyPoint v)) =
      ∫ v in Ioc (0 : ℝ) 1, (2 / Real.pi) := by
    apply setIntegral_congr_fun measurableSet_Ioc
    intro v hv
    have hm : (1 / 2 : ℝ) ≤ (cauchyPoint v : ℝ) := by
      have : v ∈ cauchyPoint ⁻¹' momentSet ∩ Ioi 0 := by
        rw [cauchyPoint_preimage_moment]
        exact hv
      exact this.1
    change (1 / 2 : ℝ) ≤ 1 / (1 + v ^ 2) at hm
    change (2 / Real.pi) * (1 + v ^ 2)⁻¹ * (1 / max (1 / (1 + v ^ 2)) (1 / 2)) = _
    rw [max_eq_left hm]
    field_simp
  rw [he]
  simp

/-- The second cutoff constant is exactly 2/pi. -/
theorem tail_integral_arcsineMeasure :
    (∫ u in tailSet, tailWeight u ∂arcsineMeasure) = 2 / Real.pi := by
  rw [setIntegral_arcsineMeasure tailWeight tailSet_measurable,
    cauchyPoint_preimage_tail]
  have he : (∫ v in Ioi (1 : ℝ), halfCauchyDensity v * tailWeight (cauchyPoint v)) =
      ∫ v in Ioi (1 : ℝ), (2 / Real.pi) * v ^ (-2 : ℝ) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro v hv
    have hm : (1 / 2 : ℝ) ≤ 1 - (cauchyPoint v : ℝ) := by
      have : v ∈ cauchyPoint ⁻¹' tailSet ∩ Ioi 0 := by
        rw [cauchyPoint_preimage_tail]
        exact hv
      have hh : (cauchyPoint v : ℝ) < 1 / 2 := this.1
      linarith
    change (1 / 2 : ℝ) ≤ 1 - 1 / (1 + v ^ 2) at hm
    have hv0 : v ≠ 0 := ne_of_gt (lt_trans zero_lt_one hv)
    change (2 / Real.pi) * (1 + v ^ 2)⁻¹ *
      (1 / max (1 - 1 / (1 + v ^ 2)) (1 / 2)) = _
    dsimp only
    rw [max_eq_left hm, Real.rpow_neg (le_of_lt (lt_trans zero_lt_one hv)), Real.rpow_two]
    have hd : (1 : ℝ) + v ^ 2 ≠ 0 := by positivity
    field_simp [hd, hv0]
    ring
  rw [he, integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) zero_lt_one]
  norm_num

end
end krylov.Strings.Tail
