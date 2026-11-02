import krylov.Strings.FeedbackAlgebra
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
Article: main_krylov, apC:eq:state and the invariant preceding apC:eq:reduced.
Use: prove the ratio invariant directly from the genuine measure integrals.
This argument includes atomic and singular continuous mass; it does not require
an unproved BV chain rule or replace the measure by a smooth density.
Source: monotonicity of the physical position state and positive integration.
-/

namespace krylov.Strings
noncomputable section
open Set MeasureTheory

/-- Slope reconstructed from the position state and the actual post-origin mass. -/
def integralSlope (μ : Measure ℝ) (φ : ℝ → ℝ) (x : ℝ) : ℝ :=
  1 + ∫ t in Ioc 0 x, φ t ∂μ

/-- Energy reconstructed from the same physical state and mass. -/
def integralEnergy (μ : Measure ℝ) (φ : ℝ → ℝ) (x : ℝ) : ℝ :=
  1 + ∫ t in Ioc 0 x, φ t ^ 2 ∂μ

/-- Energy is at least its initial unit mass, for every positive Borel measure. -/
theorem integralEnergy_one_le (μ : Measure ℝ) (φ : ℝ → ℝ) (x : ℝ) :
    1 ≤ integralEnergy μ φ x := by
  have h : 0 ≤ ∫ t in Ioc 0 x, φ t ^ 2 ∂μ :=
    setIntegral_nonneg measurableSet_Ioc (fun _ _ ↦ sq_nonneg _)
  dsimp [integralEnergy]
  linarith

/-- General-measure string invariant, proved without differentiating jumps.
Integrability is explicit; for an actual continuous position state on a finite
mass window it follows from compactness. -/
theorem integral_state_excess_nonneg {μ : Measure ℝ} {φ : ℝ → ℝ} {x : ℝ}
    (hx : 0 ≤ x) (hφ₁ : 1 ≤ φ 0) (hm : MonotoneOn φ (Icc 0 x))
    (hi : IntegrableOn φ (Ioc 0 x) μ)
    (hi₂ : IntegrableOn (fun t ↦ φ t ^ 2) (Ioc 0 x) μ) :
    0 ≤ φ x * integralSlope μ φ x - integralEnergy μ φ x := by
  have hx₀ : (0 : ℝ) ∈ Icc 0 x := ⟨le_rfl, hx⟩
  have hxx : x ∈ Icc 0 x := ⟨hx, le_rfl⟩
  have hφx : 1 ≤ φ x := hφ₁.trans (hm hx₀ hxx hx)
  have hn : 0 ≤ ∫ t in Ioc 0 x, φ x * φ t - φ t ^ 2 ∂μ := by
    apply setIntegral_nonneg measurableSet_Ioc
    intro t ht
    have ht' : t ∈ Icc 0 x := ⟨ht.1.le, ht.2⟩
    have hp : 0 ≤ φ t := zero_le_one.trans (hφ₁.trans (hm hx₀ ht' ht.1.le))
    have hle : φ t ≤ φ x := hm ht' hxx ht.2
    nlinarith
  rw [integral_sub (hi.const_mul _) hi₂, integral_const_mul] at hn
  dsimp [integralSlope, integralEnergy]
  nlinarith

/-- The Bellman ratio lies in [1,∞) for all such general-measure states. -/
theorem integral_state_ratio_ge_one {μ : Measure ℝ} {φ : ℝ → ℝ} {x : ℝ}
    (hx : 0 ≤ x) (hφ₁ : 1 ≤ φ 0) (hm : MonotoneOn φ (Icc 0 x))
    (hi : IntegrableOn φ (Ioc 0 x) μ)
    (hi₂ : IntegrableOn (fun t ↦ φ t ^ 2) (Ioc 0 x) μ) :
    1 ≤ stateRatio (φ x) (integralSlope μ φ x) (integralEnergy μ φ x) := by
  have he := integral_state_excess_nonneg hx hφ₁ hm hi hi₂
  have hK := integralEnergy_one_le μ φ x
  dsimp [stateRatio]
  apply (le_div_iff₀ (by linarith : 0 < integralEnergy μ φ x)).2
  linarith

end
end krylov.Strings
