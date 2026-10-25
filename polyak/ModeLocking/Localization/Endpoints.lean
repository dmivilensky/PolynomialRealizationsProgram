import polyak.ModeLocking.Localization.Integral

/-! The endpoint atoms are retained explicitly in the localization inequality. -/
noncomputable section
namespace polyak.ModeLocking.Localization
open Levels MeasureTheory Set
open scoped BigOperators
variable {I : Type*} [Fintype I]

theorem endpoints_complement : ({frequencyZero, frequencyPi} : Set Frequency)ᶜ =
    Threshold.interiorCarrier := by
  ext ω
  simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or,
    Threshold.interiorCarrier, mem_ofPred_eq]
  constructor
  · rintro ⟨hz,hp⟩
    exact ⟨lt_of_le_of_ne ω.property.1 (fun h => hz (Subtype.ext h.symm)),
      lt_of_le_of_ne ω.property.2 (fun h => hp (Subtype.ext h))⟩
  · rintro ⟨hz,hp⟩
    constructor
    · intro he
      have : (ω:ℝ)=0 := congrArg Subtype.val he
      linarith
    · intro he
      have : (ω:ℝ)=Real.pi := congrArg Subtype.val he
      linarith

theorem integral_endpoints_decomposition {w : Measure Frequency} [IsFiniteMeasure w]
    {f : Frequency → ℝ} (hf : Integrable f w) :
    (∫ ω, f ω ∂w) = (∫ ω in Threshold.interiorCarrier, f ω ∂w) +
      w.real {frequencyZero}*f frequencyZero + w.real {frequencyPi}*f frequencyPi := by
  have hne : frequencyZero ≠ frequencyPi := by
    intro h
    have he := congrArg Subtype.val h
    exact Real.pi_ne_zero (by simpa only [frequencyZero, frequencyPi] using he.symm)
  have he := integral_add_compl
    ((measurableSet_singleton frequencyPi).insert frequencyZero) hf
  rw [endpoints_complement] at he
  have hi : (∫ ω in ({frequencyZero,frequencyPi} : Set Frequency), f ω ∂w) =
      w.real {frequencyZero}*f frequencyZero + w.real {frequencyPi}*f frequencyPi := by
    rw [show ({frequencyZero,frequencyPi} : Set Frequency) =
      {frequencyZero} ∪ {frequencyPi} by rfl,
      setIntegral_union (disjoint_singleton.mpr hne) (measurableSet_singleton _)
        (hf.mono_measure Measure.restrict_le_self) (hf.mono_measure Measure.restrict_le_self),
      integral_singleton, integral_singleton]
    rfl
  rw [hi] at he
  linarith

theorem localization_with_endpoints (q : General.Tuning) (s t : ℝ) (n : I → ℤ)
    (a : I → ℝ) (γ : ℝ) (hT : ∀ ω, symbol q t n a γ ω ≤ 0)
    {w : Measure Frequency} [IsFiniteMeasure w]
    (hfeas : 0 ≤ ∫ ω, symbol q s n a γ ω ∂w) :
    (∫ ω in Threshold.interiorCarrier, defect q s t n a γ ω ∂w) +
      γ*w.real {frequencyZero} + |symbol q s n a γ frequencyPi| *w.real {frequencyPi} ≤
      (s-t)*(∫ ω in Threshold.interiorCarrier, budget q s n a γ ω ∂w) := by
  have hD : Integrable (defect q s t n a γ) w :=
    (continuous_defect q s t n a γ).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hB : Integrable (budget q s n a γ) w :=
    (continuous_budget q s n a γ).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hb0 : budget q s n a γ frequencyZero = 0 := by
    unfold budget
    rw [(Geometry.shiftedCurve q s).at_zero, Real.sin_pi, zero_mul]
  have hbp : budget q s n a γ frequencyPi = 0 := by
    unfold budget
    rw [(Geometry.shiftedCurve q s).at_pi, Real.sin_pi, zero_mul]
  have hd0 : defect q s t n a γ frequencyZero = γ := by simp [defect, symbol_zero]
  have hdp : defect q s t n a γ frequencyPi = |symbol q s n a γ frequencyPi| := by
    rw [defect, sineRatio_pi, one_mul, abs_of_nonpos]
    · rw [symbol_pi_shift q s t]
    · rw [symbol_pi_shift q s t]
      exact hT _
  have he := localization_integral q s t n a γ hfeas
  rw [integral_endpoints_decomposition hD, integral_endpoints_decomposition hB,
    hd0, hdp, hb0, hbp] at he
  simpa only [mul_zero, zero_mul, add_zero, mul_comm] using he

end polyak.ModeLocking.Localization
