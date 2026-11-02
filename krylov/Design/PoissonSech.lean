import krylov.Design.EvenIntegerSums
import krylov.Design.DualRemainders

/-!
Article: main_krylov, apC:lem:poisson, exact secant Poisson summation.
Use: apply mathlib's genuine Poisson theorem to the proved actual Fourier
transform and proved decay, then split the actual convergent integer sums.
Source: Poisson summation in mathlib, Euler beta--Gamma reflection for the
transform, and the independently checked hyperbolic convergence estimates.
-/

namespace krylov.Design
noncomputable section
open Real Filter MeasureTheory jacobi.Young
open scoped Topology FourierTransform

/-- The exact genuine hyperbolic-secant Poisson identity, at every positive spacing.
Article: main_krylov, apC:lem:poisson, the first displayed identity.
Proof: all continuity, physical decay, transform evaluation and frequency
summability hypotheses are discharged from the original hyperbolic function. -/
theorem poisson_sech {θ : ℝ} (hθ : 0 < θ) :
    sampledSech θ = π / (2 * θ) - 1 / 2 + π / θ * sampledSech (π ^ 2 / θ) := by
  let f : ℝ → ℂ := fun x => (sech (θ * x) : ℂ)
  have hc : Continuous f := Complex.continuous_ofReal.comp
    ((Real.continuous_cosh.comp (continuous_const.mul continuous_id)).inv₀
      (fun x => (Real.cosh_pos (θ * x)).ne'))
  have hfEven : ∀ x, f (-x) = f x := by
    intro x
    simp only [f, mul_neg, sech_neg]
  have hsPos : Summable (fun n : ℕ => f ((n : ℝ) + 1)) := by
    have hs := Complex.summable_ofReal.mpr (sampledSech_summable hθ)
    simpa only [f, mul_comm θ] using hs
  have hFEven := fourier_scaled_sech_even hθ
  have hsFPos := fourier_scaled_sech_summable_positive hθ
  have hsF := summable_even_integer (𝓕 f) hFEven hsFPos
  have hp := Real.tsum_eq_tsum_fourier_of_rpow_decay_of_summable hc
    (by norm_num : (1 : ℝ) < 2) (scaled_sech_isBigO_inv_square hθ) hsF 0
  have heq : (∑' k : ℤ, f k) = ∑' k : ℤ, 𝓕 f k := by
    simpa using hp
  rw [tsum_even_integer f hfEven hsPos, tsum_even_integer (𝓕 f) hFEven hsFPos] at heq
  have hS : (∑' n : ℕ, f ((n : ℝ) + 1)) = (sampledSech θ : ℂ) := by
    rw [sampledSech, Complex.ofReal_tsum]
    apply tsum_congr
    intro n
    simp only [f, mul_comm θ]
  have hFS : (∑' n : ℕ, 𝓕 f ((n : ℝ) + 1)) =
      ((π / θ : ℝ) : ℂ) * (sampledSech (π ^ 2 / θ) : ℂ) := by
    rw [sampledSech, Complex.ofReal_tsum, ← tsum_mul_left]
    apply tsum_congr
    intro n
    rw [fourier_scaled_sech hθ]
    rw [show π ^ 2 * ((n : ℝ) + 1) / θ = ((n : ℝ) + 1) * (π ^ 2 / θ) by ring]
  have hF0 : 𝓕 f 0 = ((π / θ : ℝ) : ℂ) := by
    rw [fourier_scaled_sech hθ]
    simp only [mul_zero, zero_div, sech, Real.cosh_zero, inv_one, Complex.ofReal_one, mul_one]
  rw [hS, hFS, hF0] at heq
  have hf0 : f 0 = 1 := by simp [f, sech]
  rw [hf0] at heq
  have hreal : 1 + 2 * sampledSech θ =
      π / θ + 2 * (π / θ * sampledSech (π ^ 2 / θ)) := by exact_mod_cast heq
  rw [show π / (2 * θ) = (π / θ) / 2 by ring]
  linarith

end
end krylov.Design
