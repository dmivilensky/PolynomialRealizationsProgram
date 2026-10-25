import polyak.ModeLocking.Localization.Shift

/-! A continuous endpoint extension of the ratio in the localization formula. -/
noncomputable section
namespace polyak.ModeLocking.Localization
open Levels MeasureTheory Set
open scoped BigOperators
variable {I : Type*} [Fintype I]

def sineRatio (q : General.Tuning) (s t : ℝ) (ω : Frequency) : ℝ :=
  Geometry.shiftRadius q t ω / Geometry.shiftRadius q s ω

theorem sineRatio_pos (q : General.Tuning) (s t : ℝ) (ω : Frequency) :
    0 < sineRatio q s t ω :=
  div_pos (Geometry.shiftRadius_pos q t ω.property) (Geometry.shiftRadius_pos q s ω.property)

theorem continuous_sineRatio (q : General.Tuning) (s t : ℝ) :
    Continuous (sineRatio q s t) := by
  have hR (u : ℝ) : Continuous (fun ω : Frequency => Geometry.shiftRadius q u ω) := by
    unfold Geometry.shiftRadius Geometry.shiftNumerator General.Tuning.Xi
    fun_prop
  exact (hR t).div (hR s) fun ω => (Geometry.shiftRadius_pos q s ω.property).ne'

theorem sineRatio_interior (q : General.Tuning) (s t : ℝ) (ω : Frequency)
    (hω : ω ∈ Threshold.interiorCarrier) :
    sineRatio q s t ω = Real.sin (Geometry.shiftedCurve q s ω) /
      Real.sin (Geometry.shiftedCurve q t ω) := by
  simp only [Geometry.shiftedCurve_apply]
  rw [Geometry.sin_shiftedAngle q s ω.property, Geometry.sin_shiftedAngle q t ω.property]
  unfold sineRatio
  field_simp [(Real.sin_pos_of_pos_of_lt_pi hω.1 hω.2).ne']

@[simp] theorem sineRatio_zero (q : General.Tuning) (s t : ℝ) :
    sineRatio q s t frequencyZero = 1 := by
  unfold sineRatio Geometry.shiftRadius Geometry.shiftNumerator
  simp [frequencyZero, Real.sqrt_sq_eq_abs, q.Xi_one_neg.ne]

@[simp] theorem sineRatio_pi (q : General.Tuning) (s t : ℝ) :
    sineRatio q s t frequencyPi = 1 := by
  unfold sineRatio Geometry.shiftRadius Geometry.shiftNumerator
  simp [frequencyPi, Real.sqrt_sq_eq_abs, q.Xi_neg_one_neg.ne]

theorem continuous_symbol (q : General.Tuning) (s : ℝ) (n : I → ℤ) (a : I → ℝ) (γ : ℝ) :
    Continuous (symbol q s n a γ) :=
  (continuous_finsetSum _ fun i _ => continuous_const.mul
    ((Geometry.shiftedCurve q s).continuous_lag (n i))).add
      (continuous_const.mul (Geometry.shiftedCurve q s).continuous_minimizer)

theorem continuous_oscillation (n : I → ℤ) (a : I → ℝ) :
    Continuous (oscillation n a) := by
  unfold oscillation
  fun_prop

theorem shift_identity_closed (q : General.Tuning) (s t : ℝ) (n : I → ℤ)
    (a : I → ℝ) (γ : ℝ) (ω : Frequency) :
    symbol q s n a γ ω = sineRatio q s t ω * symbol q t n a γ ω +
      (s-t) * (Real.sin (Geometry.shiftedCurve q s ω) * (oscillation n a ω + γ)) := by
  by_cases hz : ω = frequencyZero
  · subst ω
    rw [symbol_zero, symbol_zero, sineRatio_zero]
    have he : Geometry.shiftedCurve q s frequencyZero = Real.pi := (Geometry.shiftedCurve q s).at_zero
    rw [he, Real.sin_pi]
    ring
  by_cases hp : ω = frequencyPi
  · subst ω
    rw [sineRatio_pi]
    have he : Geometry.shiftedCurve q s frequencyPi = Real.pi := (Geometry.shiftedCurve q s).at_pi
    rw [he, Real.sin_pi]
    simpa only [one_mul, zero_mul, mul_zero, add_zero] using symbol_pi_shift q s t n a γ
  have hω : ω ∈ Threshold.interiorCarrier := by
    exact ⟨lt_of_le_of_ne ω.property.1 (fun h => hz (Subtype.ext h.symm)),
      lt_of_le_of_ne ω.property.2 (fun h => hp (Subtype.ext h))⟩
  have he := shift_identity q s t n a γ ω hω
  rw [sineRatio_interior q s t ω hω]
  have he' := (div_eq_iff (phase_sin_pos q s ω hω).ne').mp he
  rw [he']
  ring

def defect (q : General.Tuning) (s t : ℝ) (n : I → ℤ) (a : I → ℝ) (γ : ℝ)
    (ω : Frequency) : ℝ := sineRatio q s t ω * (-symbol q t n a γ ω)

def budget (q : General.Tuning) (s : ℝ) (n : I → ℤ) (a : I → ℝ) (γ : ℝ)
    (ω : Frequency) : ℝ :=
  Real.sin (Geometry.shiftedCurve q s ω) * (oscillation n a ω + γ)

theorem continuous_defect (q : General.Tuning) (s t : ℝ) (n : I → ℤ) (a : I → ℝ) (γ : ℝ) :
    Continuous (defect q s t n a γ) :=
  (continuous_sineRatio q s t).mul (continuous_symbol q t n a γ).neg

theorem continuous_budget (q : General.Tuning) (s : ℝ) (n : I → ℤ) (a : I → ℝ) (γ : ℝ) :
    Continuous (budget q s n a γ) :=
  (Real.continuous_sin.comp (Geometry.shiftedCurve q s).continuous).mul
    ((continuous_oscillation n a).add continuous_const)

theorem defect_nonneg (q : General.Tuning) (s t : ℝ) (n : I → ℤ) (a : I → ℝ)
    (γ : ℝ) (hT : ∀ ω, symbol q t n a γ ω ≤ 0) (ω : Frequency) :
    0 ≤ defect q s t n a γ ω :=
  mul_nonneg (sineRatio_pos q s t ω).le (neg_nonneg.mpr (hT ω))

theorem budget_le_two (q : General.Tuning) (s : ℝ) (n : I → ℤ) (a : I → ℝ)
    (γ : ℝ) (ha : ∀ i, 0 ≤ a i) (hγ : 0 ≤ γ) (hnorm : (∑ i, a i)+γ=1)
    (ω : Frequency) : budget q s n a γ ω ≤ 2 := by
  have hP := oscillation_add_gamma_le_two n a γ ha hγ hnorm ω
  have hpos := add_nonneg (oscillation_nonneg n a ha ω) hγ
  have hs := Real.sin_le_one (Geometry.shiftedCurve q s ω)
  unfold budget
  nlinarith

end polyak.ModeLocking.Localization
