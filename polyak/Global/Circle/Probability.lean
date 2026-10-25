import polyak.Global.Circle.Moments

/-! Symmetrization and folding preserve total mass, including probability normalization. -/
noncomputable section
namespace polyak.Global.Circle
open MeasureTheory Set
open scoped ENNReal NNReal

instance symmetrize_finite (w:Measure Levels.Frequency) [IsFiniteMeasure w] : IsFiniteMeasure (symmetrize w) := by
  constructor
  unfold symmetrize reflect
  rw [Measure.smul_apply,Measure.add_apply]
  exact ENNReal.mul_lt_top (by norm_num) (ENNReal.add_lt_top.mpr ⟨measure_lt_top _ _,measure_lt_top _ _⟩)

instance symmetrize_probability (w:Measure Levels.Frequency) [IsProbabilityMeasure w] : IsProbabilityMeasure (symmetrize w) := by
  constructor
  simp only [symmetrize,Measure.smul_apply,Measure.add_apply,reflect,
    Measure.map_apply (show Measurable embed from continuous_embed.measurable) MeasurableSet.univ,
    Measure.map_apply measurable_neg MeasurableSet.univ,preimage_univ,measure_univ]
  norm_num
  change (2:ℝ≥0∞)⁻¹*2=1
  exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)

instance folded_probability (μ:Measure Circle) [IsProbabilityMeasure μ] : IsProbabilityMeasure (folded μ) :=
  inferInstanceAs (IsProbabilityMeasure (μ.map fold))

instance folded_finite (μ:Measure Circle) [IsFiniteMeasure μ] : IsFiniteMeasure (folded μ) :=
  inferInstanceAs (IsFiniteMeasure (μ.map fold))

end polyak.Global.Circle
