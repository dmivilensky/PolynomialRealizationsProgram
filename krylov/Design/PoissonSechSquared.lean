import krylov.Design.PoissonSech

/-!
Article: main_krylov, apC:lem:poisson, the second actual Poisson formula.
Use: the squared-secant series and its weighted-cosecant dual, with genuine
summability, actual Fourier evaluation, and the zero mode checked separately.
Source: Poisson summation and the Euler beta--Gamma transform proved in the
preceding modules; no transform or series identity is assumed.
-/

namespace krylov.Design
noncomputable section
open Real Filter MeasureTheory jacobi.Young
open scoped Topology FourierTransform

/-- The genuine positive squared-secant series in the source majorant.
Article: main_krylov, apC:lem:poisson. -/
def sampledSechSquared (θ : ℝ) : ℝ := ∑' n : ℕ, sech (((n : ℝ) + 1) * θ) ^ 2

/-- Every positive-spacing squared-secant series genuinely converges.
Article: main_krylov, apC:lem:poisson. -/
theorem sampledSechSquared_summable {θ : ℝ} (hθ : 0 < θ) :
    Summable (fun n : ℕ => sech (((n : ℝ) + 1) * θ) ^ 2) := by
  apply Summable.of_nonneg_of_le (fun n => sq_nonneg _) _ (sampledSech_summable hθ)
  intro n
  have hp := sech_pos (((n : ℝ) + 1) * θ)
  have hb : sech (((n : ℝ) + 1) * θ) ≤ 1 :=
    inv_le_one_of_one_le₀ (Real.one_le_cosh _)
  nlinarith

/-- The actual squared-secant Fourier transform is even, including its removable zero mode.
Article: main_krylov, apC:lem:poisson. -/
theorem fourier_scaled_sechSquared_even {θ : ℝ} (hθ : 0 < θ) (w : ℝ) :
    𝓕 (fun x : ℝ => (sech (θ * x) : ℂ) ^ 2) (-w) =
      𝓕 (fun x : ℝ => (sech (θ * x) : ℂ) ^ 2) w := by
  by_cases hw : w = 0
  · simp only [hw, neg_zero]
  rw [fourier_scaled_sechSquared hθ (neg_ne_zero.mpr hw), fourier_scaled_sechSquared hθ hw]
  simp [mul_neg, neg_div, Real.sinh_neg, div_neg]

/-- The actual positive-frequency squared-secant Fourier series genuinely converges.
Article: main_krylov, apC:lem:poisson. -/
theorem fourier_scaled_sechSquared_summable_positive {θ : ℝ} (hθ : 0 < θ) :
    Summable (fun n : ℕ => 𝓕 (fun x : ℝ => (sech (θ * x) : ℂ) ^ 2) ((n : ℝ) + 1)) := by
  have hA : 0 < π ^ 2 / θ := div_pos (sq_pos_of_pos Real.pi_pos) hθ
  have hs := Complex.summable_ofReal.mpr (sampledWeightedCsch_summable hA)
  convert! hs.mul_left ((2 * π ^ 2 / θ ^ 2 : ℝ) : ℂ) using 1
  funext n
  rw [fourier_scaled_sechSquared hθ (by positivity)]
  rw [show π ^ 2 * ((n : ℝ) + 1) / θ = ((n : ℝ) + 1) * (π ^ 2 / θ) by ring]
  push_cast
  rfl

/-- The exact genuine squared-secant Poisson identity at every positive spacing.
Article: main_krylov, apC:lem:poisson, the second displayed identity.
Proof: the actual transform, its genuine integer summability, physical decay,
and the removable zero mode are all discharged from the original profile. -/
theorem poisson_sechSquared {θ : ℝ} (hθ : 0 < θ) :
    sampledSechSquared θ = 1 / θ - 1 / 2 +
      2 * π ^ 2 / θ ^ 2 * sampledWeightedCsch (π ^ 2 / θ) := by
  let f : ℝ → ℂ := fun x => (sech (θ * x) : ℂ) ^ 2
  have hc : Continuous f := (Complex.continuous_ofReal.comp
    ((Real.continuous_cosh.comp (continuous_const.mul continuous_id)).inv₀
      (fun x => (Real.cosh_pos (θ * x)).ne'))).pow 2
  have hfEven : ∀ x, f (-x) = f x := by
    intro x
    simp only [f, mul_neg, sech_neg]
  have hsPos : Summable (fun n : ℕ => f ((n : ℝ) + 1)) := by
    have hs := Complex.summable_ofReal.mpr (sampledSechSquared_summable hθ)
    simpa only [f, Complex.ofReal_pow, mul_comm θ] using hs
  have hFEven := fourier_scaled_sechSquared_even hθ
  have hsFPos := fourier_scaled_sechSquared_summable_positive hθ
  have hsF := summable_even_integer (𝓕 f) hFEven hsFPos
  have hp := Real.tsum_eq_tsum_fourier_of_rpow_decay_of_summable hc
    (by norm_num : (1 : ℝ) < 2) (scaled_sechSquared_isBigO_inv_square hθ) hsF 0
  have heq : (∑' k : ℤ, f k) = ∑' k : ℤ, 𝓕 f k := by simpa using hp
  rw [tsum_even_integer f hfEven hsPos, tsum_even_integer (𝓕 f) hFEven hsFPos] at heq
  have hS : (∑' n : ℕ, f ((n : ℝ) + 1)) = (sampledSechSquared θ : ℂ) := by
    rw [sampledSechSquared, Complex.ofReal_tsum]
    apply tsum_congr
    intro n
    simp only [f, mul_comm θ, Complex.ofReal_pow]
  have hFS : (∑' n : ℕ, 𝓕 f ((n : ℝ) + 1)) =
      ((2 * π ^ 2 / θ ^ 2 : ℝ) : ℂ) * (sampledWeightedCsch (π ^ 2 / θ) : ℂ) := by
    rw [sampledWeightedCsch, Complex.ofReal_tsum, ← tsum_mul_left]
    apply tsum_congr
    intro n
    rw [fourier_scaled_sechSquared hθ (by positivity)]
    rw [show π ^ 2 * ((n : ℝ) + 1) / θ = ((n : ℝ) + 1) * (π ^ 2 / θ) by ring]
    push_cast
    rfl
  have hF0 : 𝓕 f 0 = ((2 / θ : ℝ) : ℂ) := fourier_scaled_sechSquared_zero hθ
  have hf0 : f 0 = 1 := by simp [f, sech]
  rw [hS, hFS, hF0, hf0] at heq
  have hreal : 1 + 2 * sampledSechSquared θ =
      2 / θ + 2 * (2 * π ^ 2 / θ ^ 2 * sampledWeightedCsch (π ^ 2 / θ)) := by
    exact_mod_cast heq
  rw [show (2 : ℝ) / θ = 2 * (1 / θ) by ring] at hreal
  linarith

end
end krylov.Design
