import krylov.Strings.TailMeasureContinuity
import Mathlib.MeasureTheory.Measure.Portmanteau

/-!
Article: main_krylov, apC:prop:tauber, convergence of truncated integrals.
Use: pass from weak convergence of the compactified finite measures to the
two bounded tests with a single cutoff.  The cutoff is allowed to be
discontinuous only on a set of zero limiting measure.
Source: mathlib's probability portmanteau theorem, with normalization proved
here for finite measures rather than assumed as an additional hypothesis.
-/

namespace krylov.Strings.Tail
noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal

private instance : Nonempty UnitInterval := ⟨⟨0, by norm_num⟩⟩

/-- The null-boundary conclusion of portmanteau holds for finite measures;
their masses may vary and the limiting measure may be zero. -/
theorem tendsto_set_of_null_frontier {ι : Type*} {F : Filter ι}
    {μ : ι → FiniteMeasure UnitInterval} {ν : FiniteMeasure UnitInterval}
    (hweak : Tendsto μ F (𝓝 ν)) {E : Set UnitInterval}
    (hfront : ν (frontier E) = 0) :
    Tendsto (fun i ↦ μ i E) F (𝓝 (ν E)) := by
  by_cases hz : ν = 0
  · subst ν
    have hm := hweak.mass
    change Tendsto (fun i ↦ (μ i).mass) F (𝓝 0) at hm
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hm
      (fun i ↦ (zero_le : 0 ≤ μ i E)) (fun i ↦ (μ i).apply_le_mass E)
  · have hn := FiniteMeasure.tendsto_normalize_of_tendsto hweak hz
    have hf : ν.normalize (frontier E) = 0 := by
      rw [ν.normalize_eq_of_nonzero hz, hfront, mul_zero]
    have he := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto hn hf
    have hp := hweak.mass.mul he
    simpa only [← FiniteMeasure.self_eq_mass_mul_normalize] using hp

private instance continuous_weight_finite (μ : FiniteMeasure UnitInterval)
    (h : C(UnitInterval, ℝ)) :
    IsFiniteMeasure ((μ : Measure UnitInterval).withDensity
      (fun u ↦ ENNReal.ofReal (h u))) := by
  apply isFiniteMeasure_withDensity
  have hi : Integrable h (μ : Measure UnitInterval) :=
    Integrable.of_bound h.continuous.aestronglyMeasurable ‖h‖
      (Eventually.of_forall fun u ↦ h.norm_coe_le_norm u)
  have he : (fun u ↦ ENNReal.ofReal (h u)) = fun u ↦ ENNReal.ofReal (max (h u) 0) := by
    funext u
    simp
  rw [he, ← ofReal_integral_eq_lintegral_ofReal hi.pos_part
    (Eventually.of_forall fun u ↦ le_max_right (h u) 0)]
  exact ENNReal.ofReal_ne_top

/-- Weight a compact finite measure by the nonnegative part of an actual
continuous function.  This is used only with nonnegative weights below. -/
def continuousWeighted (μ : FiniteMeasure UnitInterval) (h : C(UnitInterval, ℝ)) :
    FiniteMeasure UnitInterval :=
  ⟨(μ : Measure UnitInterval).withDensity (fun u ↦ ENNReal.ofReal (h u)), inferInstance⟩

/-- Integrals against the weighted measure are the corresponding ordinary
continuous weighted integrals whenever the weight is nonnegative. -/
theorem integral_continuousWeighted (μ : FiniteMeasure UnitInterval)
    (h f : C(UnitInterval, ℝ)) (hh : ∀ u, 0 ≤ h u) :
    (∫ u, f u ∂continuousWeighted μ h) = ∫ u, h u * f u ∂μ := by
  change (∫ u, f u ∂(μ : Measure UnitInterval).withDensity _) = _
  rw [integral_withDensity_eq_integral_toReal_smul h.continuous.measurable.ennreal_ofReal
    (Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (hh _), smul_eq_mul]

/-- Multiplication by a fixed nonnegative continuous weight preserves weak
convergence of finite measures on the compact interval. -/
theorem tendsto_continuousWeighted {ι : Type*} {F : Filter ι}
    {μ : ι → FiniteMeasure UnitInterval} {ν : FiniteMeasure UnitInterval}
    (hweak : Tendsto μ F (𝓝 ν)) (h : C(UnitInterval, ℝ)) (hh : ∀ u, 0 ≤ h u) :
    Tendsto (fun i ↦ continuousWeighted (μ i) h) F (𝓝 (continuousWeighted ν h)) := by
  apply FiniteMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro f
  change Tendsto (fun i ↦ ∫ u, f.toContinuousMap u ∂continuousWeighted (μ i) h)
    F (𝓝 (∫ u, f.toContinuousMap u ∂continuousWeighted ν h))
  simp_rw [integral_continuousWeighted _ h f.toContinuousMap hh]
  exact (FiniteMeasure.continuous_integral_continuousMap (h * f.toContinuousMap)).tendsto ν |>.comp hweak

/-- The real mass of a continuously weighted measurable set is its usual
set integral.  Nonnegativity removes the positive-part convention. -/
theorem continuousWeighted_apply_real (μ : FiniteMeasure UnitInterval)
    (h : C(UnitInterval, ℝ)) (hh : ∀ u, 0 ≤ h u)
    {E : Set UnitInterval} (hE : MeasurableSet E) :
    ((continuousWeighted μ h E : ℝ≥0) : ℝ) = ∫ u in E, h u ∂μ := by
  rw [← FiniteMeasure.measureReal_eq_coe_coeFn]
  change ((μ : Measure UnitInterval).withDensity _).real E = _
  rw [measureReal_def, withDensity_apply _ hE]
  have hi : Integrable h (μ : Measure UnitInterval) :=
    Integrable.of_bound h.continuous.aestronglyMeasurable ‖h‖
      (Eventually.of_forall fun u ↦ h.norm_coe_le_norm u)
  rw [← ofReal_integral_eq_lintegral_ofReal hi.integrableOn
    (Eventually.of_forall fun u ↦ hh u), ENNReal.toReal_ofReal
      (integral_nonneg fun u ↦ hh u)]

/-- Weak convergence implies convergence of a bounded continuous weighted
cutoff if the limiting measure gives its boundary zero mass. -/
theorem tendsto_setIntegral_of_null_frontier {ι : Type*} {F : Filter ι}
    {μ : ι → FiniteMeasure UnitInterval} {ν : FiniteMeasure UnitInterval}
    (hweak : Tendsto μ F (𝓝 ν)) (h : C(UnitInterval, ℝ)) (hh : ∀ u, 0 ≤ h u)
    {E : Set UnitInterval} (hE : MeasurableSet E) (hfront : ν (frontier E) = 0) :
    Tendsto (fun i ↦ ∫ u in E, h u ∂μ i) F (𝓝 (∫ u in E, h u ∂ν)) := by
  have hz : continuousWeighted ν h (frontier E) = 0 := by
    apply (FiniteMeasure.null_iff_toMeasure_null _ _).mpr
    exact withDensity_absolutelyContinuous (ν : Measure UnitInterval) _
      ((FiniteMeasure.null_iff_toMeasure_null _ _).mp hfront)
  have ht := tendsto_set_of_null_frontier (tendsto_continuousWeighted hweak h hh) hz
  have hc := NNReal.continuous_coe.tendsto (continuousWeighted ν h E) |>.comp ht
  simpa only [Function.comp_def, continuousWeighted_apply_real _ h hh hE] using hc

end
end krylov.Strings.Tail
