import jacobi.Reference.CoefficientTransform

/-!
Article: jacobi, Proposition C.2.
The original shared Lebesgue unit interval has exactly unit measure.
The community probability-space Lp inclusion therefore gives the true
L1 bound by the actual original L2 norm, with no extra constant.
Use: the actual L1/L2 norm comparison fixes the compact GL operator norm bound in the original physical normalization.
-/
namespace jacobi.Reference
noncomputable section
open Real Set MeasureTheory
open scoped Topology
attribute [local instance] Measure.Subtype.measureSpace

/-- The genuine original reference interval has exactly unit Lebesgue measure.
Use: the actual L1/L2 norm comparison fixes the compact GL operator norm bound in the original physical normalization.
Article: jacobi, Proposition C.2.
Source: Lebesgue measure of a real interval and the community subtype measure.
Proof: the genuine subtype measure of the whole interval is the actual real interval measure, equal to its length one. -/
theorem interval_volume_univ : (volume : Measure Interval) univ=1 := by
  rw [Measure.Subtype.volume_univ measurableSet_Icc.nullMeasurableSet,Real.volume_Icc]
  norm_num

/-- The genuine L1 norm of every original reference L2 input is bounded by its actual original L2 norm.
Use: the original uniform kernel majorant bounds the true compact GL summand operator norm by the same summable inverse-square scale.
Article: jacobi, Proposition C.2.
Source: Holder's inequality, community Lp inclusion on a probability space.
Proof: the original measure has total mass one. Apply the community
Lp comparison from exponent two to exponent one. Taking genuine finite
real norms identifies the first with the actual integral of the
original absolute input and the second with its original L2 norm. -/
theorem space_L1_le_norm (v : Space) : (∫ t:Interval,‖v t‖)≤‖v‖ := by
  -- The probability measure is the original physical Lebesgue measure, not a rescaled replacement measure.
  let : IsProbabilityMeasure (volume : Measure Interval) := ⟨interval_volume_univ⟩
  have hh : eLpNorm (fun t:Interval => v t) 1 volume≤eLpNorm (fun t:Interval => v t) 2 volume :=
    eLpNorm_le_eLpNorm_of_exponent_le (by norm_num)
  rw [integral_norm_eq_lintegral_enorm (Lp.memLp v).aestronglyMeasurable,
    ← eLpNorm_one_eq_lintegral_enorm (Lp.memLp v).aestronglyMeasurable,Lp.norm_def]
  exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top v) hh

end
end jacobi.Reference
