import krylov.ContinuumBV.ActualContinuous
import krylov.ContinuumBV.PotentialDirections
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
Article: main_krylov, apC:eq:state and apC:lem:fund.
Use: identify every actual physical state increment with drift and mass
integrals. This is the concrete measure identity used in the BV chain rule;
it includes arbitrary singular and atomic mass and preserves right endpoints.
Source: additivity of half-open cumulative integrals and product integration.
-/

namespace krylov.ContinuumBV
noncomputable section
open Set Filter MeasureTheory
open krylov.Strings
open scoped Topology NNReal

/-- Difference of genuine cumulative integrals on a positive physical window. -/
theorem cumulative_integral_increment {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {μ : Measure ℝ} {f : ℝ → V} {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hi : IntegrableOn f (Ioc 0 b) μ) :
    (∫ x in Ioc 0 b, f x ∂μ) - (∫ x in Ioc 0 a, f x ∂μ) = ∫ x in Ioc a b, f x ∂μ := by
  have hsub : Ioc (0 : ℝ) a ⊆ Ioc 0 b := Ioc_subset_Ioc_right hab
  have hs : Ioc (0 : ℝ) b \ Ioc 0 a = Ioc a b := by
    ext x
    simp only [Set.mem_sdiff, mem_Ioc]
    constructor
    · intro hx
      refine ⟨?_, hx.1.2⟩
      by_contra hax
      exact hx.2 ⟨hx.1.1, le_of_not_gt hax⟩
    · intro hx
      exact ⟨⟨ha.trans_lt hx.1, hx.2⟩, fun h => (not_le_of_gt hx.1) h.2⟩
  rw [← hs]
  exact (setIntegral_sdiff measurableSet_Ioc hi hsub).symm

/-- Actual physical state at a point, without clipping the time coordinate. -/
def rawState (M : Mass) (φ : ℝ → ℝ) (x : ℝ) : PotentialState :=
  (φ x, integralSlope M.measure φ x, integralEnergy M.measure φ x)

/-- State velocity with respect to physical length dx. -/
def driftDensity (M : Mass) (φ : ℝ → ℝ) (x : ℝ) : PotentialState :=
  (integralSlope M.measure φ x, 0, 0)

/-- State velocity with respect to mass dM. -/
def massDensity (φ : ℝ → ℝ) (x : ℝ) : PotentialState := (0, φ x, φ x ^ 2)

/-- Drift density is integrable on every compact physical interval. -/
theorem driftDensity_integrable (M : Mass) {φ : ℝ → ℝ}
    (hc : Continuous φ) (hm : Monotone φ) (h₀ : φ 0 = 1) (a b : ℝ) :
    IntegrableOn (driftDensity M φ) (Ioc a b) volume := by
  have hp : IntervalIntegrable (integralSlope M.measure φ) volume a b :=
    (M.slope_monotone hc hm h₀).intervalIntegrable
  exact hp.1.prodMk ((integrable_zero _ _ _).prodMk (integrable_zero _ _ _))

/-- Mass density is genuinely integrable against the actual string mass. -/
theorem massDensity_integrable (M : Mass) {φ : ℝ → ℝ} (hc : Continuous φ) (a b : ℝ) :
    IntegrableOn (massDensity φ) (Ioc a b) M.measure := by
  have : IsFiniteMeasure (M.measure.restrict (Ioc a b)) := by
    constructor
    rw [Measure.restrict_apply_univ]
    exact M.measure_Ioc_lt_top a b
  have hφ := hc.continuousOn.integrableOn_of_subset_isCompact isCompact_Icc measurableSet_Ioc
    Ioc_subset_Icc_self (M.measure_Ioc_lt_top a b).ne
  have hφ₂ := (hc.pow 2).continuousOn.integrableOn_of_subset_isCompact isCompact_Icc measurableSet_Ioc
    Ioc_subset_Icc_self (M.measure_Ioc_lt_top a b).ne
  exact (integrable_zero _ _ _).prodMk (hφ.prodMk hφ₂)

/-- The complete state increment is exactly drift plus actual mass. No
derivative or BV chain identity is assumed; only the source integral state
equations and their normalized initialization are used. -/
theorem rawState_increment (M : Mass) {φ : ℝ → ℝ}
    (hc : Continuous φ) (hm : Monotone φ) (h₀ : φ 0 = 1) (L : ℝ≥0)
    (he : ∀ x ∈ Icc 0 (L : ℝ), φ x = 1 + ∫ t in Ioc 0 x, integralSlope M.measure φ t)
    {a b : ℝ} (ha : a ∈ Icc 0 (L : ℝ)) (hb : b ∈ Icc 0 (L : ℝ)) (hab : a ≤ b) :
    rawState M φ b - rawState M φ a =
      (∫ x in Ioc a b, driftDensity M φ x) +
        (∫ x in Ioc a b, massDensity φ x ∂M.measure) := by
  have hp0b : IntegrableOn (integralSlope M.measure φ) (Ioc 0 b) volume :=
    (driftDensity_integrable M hc hm h₀ 0 b).fst
  have hφ0b := M.position_integrable hc b
  have hφ₂0b := M.position_integrable (hc.pow 2) b
  have hpi : IntegrableOn (integralSlope M.measure φ) (Ioc a b) volume :=
    (driftDensity_integrable M hc hm h₀ a b).fst
  have hmi := massDensity_integrable M hc a b
  have hφi : IntegrableOn φ (Ioc a b) M.measure := hmi.snd.fst
  have hφ₂i : IntegrableOn (fun x => φ x ^ 2) (Ioc a b) M.measure := hmi.snd.snd
  have hφinc : φ b - φ a = ∫ x in Ioc a b, integralSlope M.measure φ x := by
    rw [he b hb, he a ha]
    have hi := cumulative_integral_increment ha.1 hab hp0b
    linarith
  have hpinc := cumulative_integral_increment ha.1 hab hφ0b
  have hKinc := cumulative_integral_increment ha.1 hab hφ₂0b
  simp only [Pi.pow_apply] at hKinc
  dsimp only [driftDensity, massDensity]
  rw [integral_pair hpi ((integrable_zero _ _ _).prodMk (integrable_zero _ _ _)),
    integral_pair (integrable_zero _ _ _) (hφi.prodMk hφ₂i),
    integral_pair (integrable_zero _ _ _) (integrable_zero _ _ _), integral_pair hφi hφ₂i]
  simp only [integral_zero]
  apply Prod.ext
  · simpa only [rawState, Prod.fst_sub, Prod.fst_add, add_zero] using hφinc
  · apply Prod.ext
    · change (1 + _) - (1 + _) = 0 + _
      linarith
    · change (1 + _) - (1 + _) = 0 + _
      linarith

end
end krylov.ContinuumBV
