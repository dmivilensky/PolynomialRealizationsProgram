import krylov.Design.HyperbolicDecay

/-!
Article: main_krylov, apC:lem:poisson, the genuine positive/negative frequency split.
Use: pass from actual positive-frequency convergence to integer convergence,
and split the convergent integer sum into the zero mode and symmetric pairs.
Source: mathlib's exact integer-series decomposition.
-/

namespace krylov.Design
noncomputable section
open Real Filter MeasureTheory jacobi.Young
open scoped Topology FourierTransform

/-- Positive natural-frequency convergence of an even real-variable function gives genuine integer-frequency convergence.
Article: main_krylov, apC:lem:poisson. -/
theorem summable_even_integer (f : ℝ → ℂ) (he : ∀ x, f (-x) = f x)
    (hs : Summable (fun n : ℕ => f ((n : ℝ) + 1))) : Summable (fun k : ℤ => f k) := by
  have hp : Summable (fun n : ℕ => f (((n : ℤ) + 1 : ℤ) : ℝ)) := by
    simpa only [Int.cast_add, Int.cast_natCast, Int.cast_one] using hs
  have hn : Summable (fun n : ℕ => f ((-((n : ℤ) + 1) : ℤ) : ℝ)) := by
    simpa only [Int.cast_neg, he, Int.cast_add, Int.cast_natCast, Int.cast_one] using hs
  exact hp.of_add_one_of_neg_add_one hn

/-- The actual convergent integer sum of an even function is its zero mode plus two positive-frequency sums.
Article: main_krylov, apC:lem:poisson. -/
theorem tsum_even_integer (f : ℝ → ℂ) (he : ∀ x, f (-x) = f x)
    (hs : Summable (fun n : ℕ => f ((n : ℝ) + 1))) :
    (∑' k : ℤ, f k) = f 0 + 2 * ∑' n : ℕ, f ((n : ℝ) + 1) := by
  have hp : Summable (fun n : ℕ => f (((n : ℤ) + 1 : ℤ) : ℝ)) := by
    simpa only [Int.cast_add, Int.cast_natCast, Int.cast_one] using hs
  have hn : Summable (fun n : ℕ => f ((-((n : ℤ) + 1) : ℤ) : ℝ)) := by
    simpa only [Int.cast_neg, he, Int.cast_add, Int.cast_natCast, Int.cast_one] using hs
  rw [tsum_of_add_one_of_neg_add_one (f := fun k : ℤ => f k) hp hn]
  simp only [Int.cast_neg, he, Int.cast_add, Int.cast_natCast, Int.cast_one, Int.cast_zero]
  ring

/-- The positive-frequency actual normalized sech transform is genuinely summable.
Article: main_krylov, apC:lem:poisson. -/
theorem fourier_scaled_sech_summable_positive {θ : ℝ} (hθ : 0 < θ) :
    Summable (fun n : ℕ => 𝓕 (fun x : ℝ => (sech (θ * x) : ℂ)) ((n : ℝ) + 1)) := by
  have hA : 0 < π ^ 2 / θ := div_pos (sq_pos_of_pos Real.pi_pos) hθ
  have hs : Summable (fun n : ℕ => (sech (((n : ℝ) + 1) * (π ^ 2 / θ)) : ℂ)) :=
    Complex.summable_ofReal.mpr (sampledSech_summable hA)
  convert! hs.mul_left ((π / θ : ℝ) : ℂ) using 1
  funext n
  rw [fourier_scaled_sech hθ]
  rw [show π ^ 2 * ((n : ℝ) + 1) / θ = ((n : ℝ) + 1) * (π ^ 2 / θ) by ring]

/-- The actual normalized sech transform is even.
Article: main_krylov, apC:lem:poisson. -/
theorem fourier_scaled_sech_even {θ : ℝ} (hθ : 0 < θ) (w : ℝ) :
    𝓕 (fun x : ℝ => (sech (θ * x) : ℂ)) (-w) = 𝓕 (fun x : ℝ => (sech (θ * x) : ℂ)) w := by
  rw [fourier_scaled_sech hθ, fourier_scaled_sech hθ]
  simp only [mul_neg, neg_div, sech_neg]

end
end krylov.Design
