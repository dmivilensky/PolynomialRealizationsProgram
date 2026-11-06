import chebyshev1.SineJacobi.FirstStep
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex

/-! Closed finite cotangent formula for the first Green diagonal. -/
namespace chebyshev1.SineJacobi
noncomputable section
open Real
open scoped BigOperators

theorem sine_normalization (N : ℕ) (hN : 0 < N) :
    sin (π / (2 * (N : ℝ))) * ∑ j : Fin N, sin (nodeAngle N j) = 1 := by
  have hn : (N : ℝ) ≠ 0 := by positivity
  have h := sin_mul_sum_sin N (π / (N : ℝ)) (π / (2 * (N : ℝ)))
  have h₁ : (π / (N : ℝ)) / 2 = π / (2 * (N : ℝ)) := by ring
  have h₂ : (N : ℝ) * (π / (N : ℝ)) / 2 = π / 2 := by field_simp
  have h₃ : ((N : ℝ) - 1) * (π / (N : ℝ)) / 2 +
      π / (2 * (N : ℝ)) = π / 2 := by field_simp; ring
  rw [h₁, h₂, h₃, sin_pi_div_two, one_mul] at h
  rw [← Fin.sum_univ_eq_sum_range] at h
  convert h using 1
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  dsimp [nodeAngle]
  ring

theorem sineWeight_closed (N : ℕ) (hN : 0 < N) (j : Fin N) :
    sineWeight N j = sin (π / (2 * (N : ℝ))) * sin (nodeAngle N j) := by
  have hn := sine_normalization N hN
  have hs : (∑ j : Fin N, sin (nodeAngle N j)) ≠ 0 := by
    intro he
    rw [he, mul_zero] at hn
    norm_num at hn
  dsimp [sineWeight]
  field_simp
  linear_combination -sin (nodeAngle N j) * hn

theorem sin_div_one_sub_cos (x : ℝ) (hx : 0 < x) (hπ : x < π) :
    sin x / (1 - cos x) = cot (x / 2) := by
  have hs : sin (x / 2) ≠ 0 := (sin_pos_of_pos_of_lt_pi (by linarith)
    (by linarith)).ne'
  have harg : x = 2 * (x / 2) := by ring
  conv_lhs => rw [harg, sin_two_mul, cos_two_mul_eq_one_sub]
  rw [cot_eq_cos_div_sin]
  field_simp
  ring

theorem first_green_cotangent_sum (N : ℕ) (hN : 0 < N) :
    greenWeight N 0 = sin (π / (2 * (N : ℝ))) *
      ∑ j : Fin N, cot (nodeAngle N j / 2) := by
  rw [first_green_spectral_sum N hN, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [sineWeight_closed N hN, mul_div_assoc, node,
    sin_div_one_sub_cos _ (nodeAngle_mem N j).1 (nodeAngle_mem N j).2]

end
end chebyshev1.SineJacobi
