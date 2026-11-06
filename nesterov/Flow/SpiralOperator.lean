import nesterov.Flow.SpiralReduction
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
Article: Appendix B, the Lipschitz bound for forced spiral gradients.
Use: one actual continuous real-linear diagonal operator acts on the entire
orbit and therefore controls every time pair as well as the minimizer.
-/

noncomputable section

namespace nesterov.Flow

open scoped InnerProductSpace

variable {J : Type*} [Fintype J]

def Spectrum.gradientLinearMap (ν : Spectrum J) (θ m c : ℝ) :
    EuclideanSpace ℂ J →ₗ[ℝ] EuclideanSpace ℂ J where
  toFun u := WithLp.toLp 2 (fun j => spiralMultiplier θ m c (ν.frequency j) * u j)
  map_add' u v := by
    apply (WithLp.ext_iff 2).mpr
    funext j
    change _ * (u j + v j) = _ * u j + _ * v j
    ring
  map_smul' a u := by
    apply (WithLp.ext_iff 2).mpr
    funext j
    change _ * ((a : ℂ) * u j) = (a : ℂ) * (_ * u j)
    ring

def Spectrum.gradientOperator (ν : Spectrum J) (θ m c : ℝ) :
    EuclideanSpace ℂ J →L[ℝ] EuclideanSpace ℂ J :=
  (ν.gradientLinearMap θ m c).toContinuousLinearMap

theorem Spectrum.forcedGradient_eq_operator (ν : Spectrum J) (θ m c t : ℝ) :
    ν.forcedGradient θ m c t = ν.gradientOperator θ m c (ν.orbit c t) := rfl

theorem Spectrum.forcedGradient_lipschitz (ν : Spectrum J) (θ m c s t : ℝ) :
    ‖ν.forcedGradient θ m c s - ν.forcedGradient θ m c t‖ ≤
      ‖ν.gradientOperator θ m c‖ * ‖ν.orbit c s - ν.orbit c t‖ := by
  rw [ν.forcedGradient_eq_operator, ν.forcedGradient_eq_operator, ← map_sub]
  exact (ν.gradientOperator θ m c).le_opNorm _

theorem Spectrum.forcedGradient_norm_le (ν : Spectrum J) (θ m c t : ℝ) :
    ‖ν.forcedGradient θ m c t‖ ≤ ‖ν.gradientOperator θ m c‖ * Real.exp (-c * t) := by
  rw [ν.forcedGradient_eq_operator, ← ν.orbit_norm c t]
  exact (ν.gradientOperator θ m c).le_opNorm _

theorem Spectrum.minimizer_gap_moment (ν : Spectrum J) {c : ℝ} (_hc : 0 < c) (θ m : ℝ) :
    (∑ j, ν.weight j * atomMinimizerGap θ m c (ν.frequency j)) =
      ((3 * c - θ) * (∑ j, ν.weight j * ν.frequency j ^ 2) - c * delta θ m c) / (2 * c) := by
  simp only [atomMinimizerGap, ← mul_div_assoc]
  rw [← Finset.sum_div]
  congr 1
  simp only [mul_sub, Finset.sum_sub_distrib]
  rw [← Finset.sum_mul, ν.weight_sum, one_mul]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem Spectrum.minimizer_gap_nonneg (ν : Spectrum J) {θ m c : ℝ} (hc : 0 < c)
    (h : ν.Feasible θ m c) (t : ℝ) :
    0 ≤ ⟪ν.forcedGradient θ m c t, ν.orbit c t⟫_ℝ - ν.orbitValue θ m c t := by
  rw [ν.minimizer_gap hc, ν.minimizer_gap_moment hc]
  exact mul_nonneg (Real.exp_pos _).le (div_nonneg (by linarith [h.2.2]) (by positivity))

theorem Spectrum.orbitValue_nonneg (ν : Spectrum J) {θ m c : ℝ} (hc : 0 < c)
    (hct : c ≤ θ / 2) (h : ν.Feasible θ m c) (t : ℝ) :
    0 ≤ ν.orbitValue θ m c t :=
  (ν.minimizer_gap_nonneg hc h t).trans (ν.value_ge_minimizer_gap hc hct t)

end nesterov.Flow
