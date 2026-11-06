import chebyshev1.Stepsize.LowerBound
import chebyshev1.Prefix.Gain

/-! A strict finite-horizon comparison with the prefix recurrence. -/
namespace chebyshev1.Stepsize
noncomputable section
variable (I : SpectralInterval)

theorem lowerBound_square_sub_prefix_gain_square (N : ℕ) (hN : 1 ≤ N) :
    (lowerBound I N) ^ 2 - ((Prefix.realization I).gain I N) ^ 2 =
      8 * (I.epsilon N) ^ 2 / (3 * I.delta ^ 2) *
        (N : ℝ) * (N - 1) * ((N : ℝ) ^ 2 - N + 1) := by
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hp : 0 ≤ Prefix.shape N := by
    unfold Prefix.shape
    have h1 : 0 ≤ (N : ℝ) - 1 := by linarith
    have h2 : 0 ≤ 2 * (N : ℝ) - 1 := by linarith
    positivity
  rw [lowerBound, Prefix.gain_exact I N hN, mul_pow, mul_pow,
    Real.sq_sqrt (by positivity), Real.sq_sqrt hp]
  unfold Prefix.shape
  ring

/-- Every terminally exact stepsize schedule has this explicit squared-gain gap. -/
theorem gain_square_sub_prefix_gain_square (gamma : ℕ → ℝ) (N : ℕ) (hN : 1 ≤ N)
    (h : FinalExact gamma I N) :
    8 * (I.epsilon N) ^ 2 / (3 * I.delta ^ 2) *
        (N : ℝ) * (N - 1) * ((N : ℝ) ^ 2 - N + 1) ≤
      ((realization gamma).gain I N) ^ 2 - ((Prefix.realization I).gain I N) ^ 2 := by
  rw [← lowerBound_square_sub_prefix_gain_square I N hN]
  have hn : 0 ≤ lowerBound I N := by
    unfold lowerBound SpectralInterval.epsilon
    positivity [I.den_pos N, I.delta_pos]
  have hb := (sq_le_sq₀ hn ((realization gamma).gain_nonneg I N)).mpr
    (gain_lower_bound gamma I N hN h)
  linarith

theorem prefix_gap_pos (N : ℕ) (hN : 2 ≤ N) :
    0 < 8 * (I.epsilon N) ^ 2 / (3 * I.delta ^ 2) *
      (N : ℝ) * (N - 1) * ((N : ℝ) ^ 2 - N + 1) := by
  have hn : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have he : 0 < I.epsilon N := one_div_pos.mpr (I.den_pos N)
  have hp : 0 < (N : ℝ) ^ 2 - N + 1 := by nlinarith [sq_nonneg ((N : ℝ) - 1)]
  exact mul_pos (mul_pos (mul_pos (div_pos (mul_pos (by norm_num) (sq_pos_of_pos he))
    (mul_pos (by norm_num) (sq_pos_of_pos I.delta_pos))) (by linarith)) (by linarith)) hp

/-- The comparison is strict for every horizon of at least two steps. -/
theorem prefix_gain_lt (gamma : ℕ → ℝ) (N : ℕ) (hN : 2 ≤ N)
    (h : FinalExact gamma I N) :
    (Prefix.realization I).gain I N < (realization gamma).gain I N := by
  have hg := gain_square_sub_prefix_gain_square I gamma N (by omega) h
  have hp := prefix_gap_pos I N hN
  have hleft := (Prefix.realization I).gain_nonneg I N
  have hright := (realization gamma).gain_nonneg I N
  nlinarith

end
end chebyshev1.Stepsize
