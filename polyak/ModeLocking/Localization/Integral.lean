import polyak.ModeLocking.Localization.Defect
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! Quantitative localization for genuine finite measures, including atoms. -/
noncomputable section
namespace polyak.ModeLocking.Localization
open Levels MeasureTheory Set
open scoped BigOperators
variable {I : Type*} [Fintype I]

theorem integral_symbol_nonneg (q : General.Tuning) (s : ℝ) (n : I → ℤ)
    (a : I → ℝ) (γ : ℝ) (ha : ∀ i, 0 ≤ a i) (hγ : 0 ≤ γ)
    {w : Measure Frequency} [IsFiniteMeasure w]
    (hmin : 0 ≤ ∫ ω, (Geometry.shiftedCurve q s).minimizer ω ∂w)
    (hlag : ∀ i, 0 ≤ ∫ ω, (Geometry.shiftedCurve q s).lag (n i) ω ∂w) :
    0 ≤ ∫ ω, symbol q s n a γ ω ∂w := by
  have hi (i : I) : Integrable (fun ω => a i*(Geometry.shiftedCurve q s).lag (n i) ω) w :=
    (integrable_curve_lag _ _ _).const_mul _
  unfold symbol
  rw [integral_add (integrable_finsetSum _ (fun i _ => hi i))
    ((integrable_curve_minimizer _ _).const_mul _), integral_finsetSum _ (fun i _ => hi i),
    integral_const_mul]
  simp only [integral_const_mul]
  exact add_nonneg (Finset.sum_nonneg fun i _ => mul_nonneg (ha i) (hlag i))
    (mul_nonneg hγ hmin)

theorem localization_integral (q : General.Tuning) (s t : ℝ) (n : I → ℤ)
    (a : I → ℝ) (γ : ℝ) {w : Measure Frequency} [IsFiniteMeasure w]
    (hfeas : 0 ≤ ∫ ω, symbol q s n a γ ω ∂w) :
    (∫ ω, defect q s t n a γ ω ∂w) ≤
      (s-t) * (∫ ω, budget q s n a γ ω ∂w) := by
  have hD : Integrable (defect q s t n a γ) w := (continuous_defect q s t n a γ).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  have hB : Integrable (budget q s n a γ) w := (continuous_budget q s n a γ).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  have he : (∫ ω, symbol q s n a γ ω ∂w) =
      -(∫ ω, defect q s t n a γ ω ∂w) +
        (s-t)*(∫ ω, budget q s n a γ ω ∂w) := by
    have hf : symbol q s n a γ = fun ω => -defect q s t n a γ ω +
        (s-t)*budget q s n a γ ω := by
      funext ω
      rw [shift_identity_closed q s t n a γ ω]
      unfold defect budget
      ring
    rw [hf]
    change (∫ ω, -defect q s t n a γ ω + (s-t)*budget q s n a γ ω ∂w) = _
    rw [integral_add (f := fun ω => -defect q s t n a γ ω)
      (g := fun ω => (s-t)*budget q s n a γ ω) hD.neg (hB.const_mul _),
      integral_neg, integral_const_mul]
  linarith

theorem localization_mass_bound (q : General.Tuning) (s t : ℝ) (n : I → ℤ)
    (a : I → ℝ) (γ : ℝ) (ha : ∀ i, 0 ≤ a i) (hγ : 0 ≤ γ)
    (hnorm : (∑ i, a i)+γ=1) (hst : t ≤ s)
    {w : Measure Frequency} [IsFiniteMeasure w]
    (hfeas : 0 ≤ ∫ ω, symbol q s n a γ ω ∂w) :
    (∫ ω, defect q s t n a γ ω ∂w) ≤ 2*(s-t)*w.real univ := by
  have hB : Integrable (budget q s n a γ) w := (continuous_budget q s n a γ).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  have hb := integral_mono hB (integrable_const (2:ℝ))
    (budget_le_two q s n a γ ha hγ hnorm)
  simp only [integral_const, smul_eq_mul] at hb
  have hd := localization_integral q s t n a γ hfeas
  nlinarith [mul_le_mul_of_nonneg_left hb (sub_nonneg.mpr hst)]

theorem atom_defect_bound (q : General.Tuning) (s t : ℝ) (n : I → ℤ)
    (a : I → ℝ) (γ : ℝ) (ha : ∀ i, 0 ≤ a i) (hγ : 0 ≤ γ)
    (hnorm : (∑ i, a i)+γ=1) (hst : t ≤ s)
    (hT : ∀ ω, symbol q t n a γ ω ≤ 0)
    {w : Measure Frequency} [IsFiniteMeasure w]
    (hfeas : 0 ≤ ∫ ω, symbol q s n a γ ω ∂w) (x : Frequency) :
    w.real {x} * defect q s t n a γ x ≤ 2*(s-t)*w.real univ := by
  have hi : Integrable (defect q s t n a γ) w := (continuous_defect q s t n a γ).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  have hs := integral_mono_measure (μ := w.restrict {x}) (ν := w)
    Measure.restrict_le_self (Filter.Eventually.of_forall (defect_nonneg q s t n a γ hT)) hi
  rw [integral_singleton] at hs
  exact hs.trans (localization_mass_bound q s t n a γ ha hγ hnorm hst hfeas)

end polyak.ModeLocking.Localization
