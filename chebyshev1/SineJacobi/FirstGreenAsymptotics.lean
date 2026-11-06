import chebyshev1.SineJacobi.CotangentQuadrature
import chebyshev1.Analysis.HalfHarmonic
import Mathlib.Analysis.Asymptotics.Defs

/-! The first Green diagonal grows logarithmically, with the sharp additive constant. -/
namespace chebyshev1.SineJacobi
noncomputable section
open Real Filter
open scoped Topology Asymptotics

theorem first_green_regularized (N : ℕ) (hN : 0 < N) :
    greenWeight N 0 = sinc (π / (2 * (N : ℝ))) *
      (Analysis.halfHarmonic N + (π / 2) * Analysis.midpointSum regularCotangent N) := by
  rw [first_green_regularized_sum N hN, Analysis.halfHarmonic_eq_sum]

theorem sinc_first_green_error_bound (N : ℕ) (hN : 0 < N) :
    |sinc (π / (2 * (N : ℝ))) - 1| ≤ (π ^ 2 / 24) / (N : ℝ) ^ 2 := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  let h := π / (2 * (N : ℝ))
  have hh : 0 < h := by dsimp [h]; positivity
  have hb := abs_sub_sin_le h
  rw [abs_sub_comm h (sin h), abs_of_pos hh] at hb
  calc
    _ = |sin h - h| / h := by
      rw [sinc_of_ne_zero hh.ne', ← div_self hh.ne', ← sub_div, abs_div, abs_of_pos hh]
    _ ≤ (h ^ 3 / 6) / h := div_le_div_of_nonneg_right hb hh.le
    _ = _ := by dsimp [h]; field_simp; ring

theorem first_green_constant :
    2 * log 2 + log (2 / π) = log (8 / π) := by
  have h8 : log (8 : ℝ) = 3 * log 2 := by
    calc
      _ = log ((2 : ℝ) ^ 3) := by norm_num
      _ = _ := log_pow 2 3
  rw [log_div (by norm_num : (2 : ℝ) ≠ 0) pi_ne_zero,
    log_div (by norm_num : (8 : ℝ) ≠ 0) pi_ne_zero, h8]
  ring

/-- A finite bound valid also at `N = 1`; the extra one avoids `log 1 = 0`. -/
theorem first_green_error_bound :
    ∃ C, 0 ≤ C ∧ ∀ N : ℕ, 0 < N →
      |greenWeight N 0 - (log N + eulerMascheroniConstant + log (8 / π))| ≤
        C * (log N + 1) / (N : ℝ) ^ 2 := by
  obtain ⟨M, hM, hquad⟩ := regularCotangent_midpoint_bound
  let B : ℝ := π ^ 2 / 24
  let K : ℝ := |eulerMascheroniConstant + log (8 / π)|
  let C : ℝ := (8 + M) + B * (K + 1)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hK : 0 ≤ K := abs_nonneg _
  have hH : 0 ≤ 8 + M := by linarith
  refine ⟨C, add_nonneg hH (mul_nonneg hB (by linarith)), fun N hN => ?_⟩
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hlog : 0 ≤ log (N : ℝ) := log_nonneg hn1
  let A : ℝ := log N + eulerMascheroniConstant + log (8 / π)
  let s : ℝ := sinc (π / (2 * (N : ℝ)))
  let H : ℝ := Analysis.halfHarmonic N - (log N + 2 * log 2 + eulerMascheroniConstant)
  let Q : ℝ := (π / 2) * Analysis.midpointSum regularCotangent N - log (2 / π)
  have hs : |s| ≤ 1 := abs_sinc_le_one _
  have hs1 : |s - 1| ≤ B / (N : ℝ) ^ 2 := sinc_first_green_error_bound N hN
  have hHbound : |H| ≤ 8 / (N : ℝ) ^ 2 := Analysis.halfHarmonic_error_bound N hN
  have hQbound : |Q| ≤ M / (N : ℝ) ^ 2 := hquad N hN
  have hHQ : |H + Q| ≤ (8 + M) / (N : ℝ) ^ 2 :=
    (abs_add_le H Q).trans ((add_le_add hHbound hQbound).trans_eq (by ring))
  have hA : |A| ≤ log N + K := by
    calc
      _ = |log (N : ℝ) + (eulerMascheroniConstant + log (8 / π))| := by
        dsimp [A]; congr 1; ring
      _ ≤ |log (N : ℝ)| + K := abs_add_le _ _
      _ = _ := by rw [abs_of_nonneg hlog]
  have he : greenWeight N 0 - A = s * (H + Q) + (s - 1) * A := by
    rw [first_green_regularized N hN]
    dsimp [A, s, H, Q]
    have hc := first_green_constant
    linear_combination (sinc (π / (2 * (N : ℝ)))) * hc
  have hlogK : log (N : ℝ) + K ≤ (K + 1) * (log N + 1) := by
    nlinarith [mul_nonneg hK hlog]
  change |greenWeight N 0 - A| ≤ _
  rw [he]
  calc
    _ ≤ |s * (H + Q)| + |(s - 1) * A| := abs_add_le _ _
    _ = |s| * |H + Q| + |s - 1| * |A| := by rw [abs_mul, abs_mul]
    _ ≤ 1 * ((8 + M) / (N : ℝ) ^ 2) + (B / (N : ℝ) ^ 2) * (log N + K) :=
      add_le_add (mul_le_mul hs hHQ (abs_nonneg _) (by norm_num))
        (mul_le_mul hs1 hA (abs_nonneg _) (div_nonneg hB (sq_nonneg _)))
    _ ≤ ((8 + M) / (N : ℝ) ^ 2) * (log N + 1) +
        (B / (N : ℝ) ^ 2) * ((K + 1) * (log N + 1)) := by
      apply add_le_add
      · simpa only [one_mul, mul_one] using
          mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ log N + 1 by linarith)
            (div_nonneg hH (sq_nonneg _))
      · exact mul_le_mul_of_nonneg_left hlogK (div_nonneg hB (sq_nonneg _))
    _ = _ := by dsimp [C]; ring

/-- The remainder is `O(log N / N²)`, with the Euler constant and `log(8/π)` explicit. -/
theorem first_green_error_isBigO :
    (fun N : ℕ => greenWeight N 0 - (log N + eulerMascheroniConstant + log (8 / π)))
      =O[atTop] (fun N : ℕ => log N / (N : ℝ) ^ 2) := by
  obtain ⟨C, hC, hbound⟩ := first_green_error_bound
  apply Asymptotics.IsBigO.of_bound (2 * C)
  filter_upwards [eventually_ge_atTop (4 : ℕ)] with N hN
  have hn : (4 : ℝ) ≤ N := by exact_mod_cast hN
  have hlog : 1 ≤ log (N : ℝ) := by
    apply (le_log_iff_exp_le (by linarith : (0 : ℝ) < N)).mpr
    exact exp_one_lt_d9.le.trans (by linarith)
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (show 0 ≤ log (N : ℝ) / (N : ℝ) ^ 2 from
      div_nonneg (by linarith) (sq_nonneg _))]
  calc
    _ ≤ C * (log N + 1) / (N : ℝ) ^ 2 := hbound N (by omega)
    _ ≤ C * (2 * log N) / (N : ℝ) ^ 2 := by gcongr; linarith
    _ = _ := by ring

end
end chebyshev1.SineJacobi
