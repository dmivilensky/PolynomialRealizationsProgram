import polyak.ModeLocking.Localization.Potential

/-! The locking inequality is an inequality for arbitrary genuine feasible
measures, not merely periodic or finitely atomic competitors. -/
noncomputable section
namespace polyak.ModeLocking.Localization
open Levels MeasureTheory Set
open scoped BigOperators
variable {q : General.Tuning} {t : ℝ} {L : ℕ}

def regularBudget (D : RegularData q t L) (s : ℝ) (ω : Frequency) : ℝ :=
  budget q s (fun i : {n // n ∈ D.lags} => i.val) (fun i => D.dual i) 0 ω

theorem regularBudget_pos (D : RegularData q t L) (s : ℝ) (ω : Frequency)
    (hω : ω ∈ Threshold.interiorCarrier) : 0 < regularBudget D s ω := by
  unfold regularBudget budget
  rw [add_zero, regularOscillation_eq D]
  exact mul_pos (phase_sin_pos q s ω hω) (regular_pinning_pos D ω hω.1)

theorem regularBudget_nonneg (D : RegularData q t L) (s : ℝ) (ω : Frequency) :
    0 ≤ regularBudget D s ω := by
  unfold regularBudget budget
  apply mul_nonneg (Threshold.phase_sine_nonneg _ ω)
  exact add_nonneg (oscillation_nonneg (fun i : {n // n ∈ D.lags} => i.val)
    (fun i => D.dual i) (fun i => (D.dual_pos i i.property).le) ω) le_rfl

theorem feasible_charges_interior (q : General.Tuning) (s : ℝ)
    {w : Measure Frequency} (hw : ProgramSolution (Geometry.shiftedCurve q s) nonzeroLags w) :
    0 < w Threshold.interiorCarrier := by
  apply pos_iff_ne_zero.mpr
  intro hz
  exact hw.remove_endpoints.2.1 (Measure.restrict_eq_zero.mpr hz)

theorem regularBudget_integral_pos (D : RegularData q t L) (s : ℝ)
    {w : Measure Frequency} (hw : ProgramSolution (Geometry.shiftedCurve q s) nonzeroLags w) :
    0 < ∫ ω, regularBudget D s ω ∂w := by
  have : IsFiniteMeasure w := hw.1
  have hi : Integrable (regularBudget D s) w :=
    (continuous_budget q s (fun i : {n // n ∈ D.lags} => i.val) (fun i => D.dual i) 0).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [integral_pos_iff_support_of_nonneg (regularBudget_nonneg D s) hi]
  apply (feasible_charges_interior q s hw).trans_le
  apply measure_mono
  intro ω hω
  exact (regularBudget_pos D s ω hω).ne'

theorem weightedPotential_eq_defect (D : RegularData q t L) (s : ℝ) (ω : Frequency)
    (hω : ω ∈ Threshold.interiorCarrier) :
    regularBudget D s ω * regularPotential D ω =
      defect q s t (fun i : {n // n ∈ D.lags} => i.val) (fun i => D.dual i) 0 ω := by
  unfold regularBudget budget regularPotential defect
  rw [add_zero, regularOscillation_eq D, regularSymbol_eq D t ω,
    sineRatio_interior q s t ω hω]
  field_simp [(phase_sin_pos q t ω hω).ne', (regular_pinning_pos D ω hω.1).ne']

theorem regular_average_locking (D : RegularData q t L) (s : ℝ)
    {w : Measure Frequency} (hw : ProgramSolution (Geometry.shiftedCurve q s) nonzeroLags w) :
    (∫ ω in Threshold.interiorCarrier, regularBudget D s ω * regularPotential D ω ∂w) /
      (∫ ω, regularBudget D s ω ∂w) ≤ s-t := by
  have : IsFiniteMeasure w := hw.1
  let n : {n // n ∈ D.lags} → ℤ := fun i => i.val
  let a : {n // n ∈ D.lags} → ℝ := fun i => D.dual i
  have hT : ∀ ω, symbol q t n a 0 ω ≤ 0 := by
    intro ω
    rw [regularSymbol_eq D t ω]
    exact D.symbol_nonpos ω ω.property
  have hfeas : 0 ≤ ∫ ω, symbol q s n a 0 ω ∂w :=
    integral_symbol_nonneg q s n a 0 (fun i => (D.dual_pos i i.property).le) le_rfl
      hw.2.2.1 (fun i => hw.2.2.2 i.val (D.lags_nonzero i i.property))
  have hb := localization_with_endpoints q s t n a 0 hT hfeas
  have hnum : (∫ ω in Threshold.interiorCarrier, regularBudget D s ω * regularPotential D ω ∂w) =
      ∫ ω in Threshold.interiorCarrier, defect q s t n a 0 ω ∂w := by
    apply setIntegral_congr_fun Threshold.measurableSet_interiorCarrier
    intro ω hω
    exact weightedPotential_eq_defect D s ω hω
  have hden : (∫ ω, regularBudget D s ω ∂w) =
      ∫ ω in Threshold.interiorCarrier, regularBudget D s ω ∂w := by
    have hi : Integrable (regularBudget D s) w :=
      (continuous_budget q s n a 0).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    rw [integral_endpoints_decomposition hi]
    have hz : regularBudget D s frequencyZero = 0 := by
      unfold regularBudget budget
      rw [(Geometry.shiftedCurve q s).at_zero, Real.sin_pi,zero_mul]
    have hp : regularBudget D s frequencyPi = 0 := by
      unfold regularBudget budget
      rw [(Geometry.shiftedCurve q s).at_pi, Real.sin_pi,zero_mul]
    rw [hz,hp,mul_zero,mul_zero,add_zero,add_zero]
  apply (div_le_iff₀ (regularBudget_integral_pos D s hw)).mpr
  rw [hnum,hden]
  have hmass : 0 ≤ |symbol q s n a 0 frequencyPi| * w.real {frequencyPi} :=
    mul_nonneg (abs_nonneg _) ENNReal.toReal_nonneg
  simp only [zero_mul, add_zero] at hb
  exact (le_add_of_nonneg_right hmass).trans hb

end polyak.ModeLocking.Localization
