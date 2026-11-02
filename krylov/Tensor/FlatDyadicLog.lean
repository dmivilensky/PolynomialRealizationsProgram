import krylov.Tensor.FlatDyadicCost
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
Article: main_krylov, apG:flat, explicit logarithmic constant.
Use: convert the actual dyadic decomposition cost to the printed constant ten.
Source: standard ceiling binary logarithm and finite geometric sum; all
rounding and numerical inequalities are proved here.
-/

namespace krylov.Tensor
noncomputable section

/-- The ceiling binary logarithm gives exactly the dyadic cover required by the
actual prefix decomposition. Article: main_krylov, apG:flat. -/
theorem flat_dyadic_cover {N : ℕ} (hN : 2 ≤ N) :
    N ≤ 2 ^ Nat.clog 2 N ∧ (2 : ℝ) ^ Nat.clog 2 N < 2 * (N : ℝ) := by
  have hL := Nat.clog_pos (by decide : 1 < 2) (by omega : 1 < N)
  have hp := Nat.pow_pred_clog_lt_self (by decide : 1 < 2) (by omega : 1 < N)
  refine ⟨Nat.le_pow_clog (by decide) N, ?_⟩
  have hpow : (2 : ℝ) ^ (Nat.clog 2 N - 1) < (N : ℝ) := by exact_mod_cast hp
  rw [show Nat.clog 2 N = (Nat.clog 2 N - 1) + 1 by omega, pow_succ]
  linarith

/-- The harmless extra logarithmic level absorbs the second flat tensor term.
Article: main_krylov, apG:flat. -/
theorem flat_dyadic_log_margin {N : ℕ} (hN : 2 ≤ N) :
    (Nat.clog 2 N : ℝ) + 1 ≤ Real.logb 2 (4 * (N : ℝ)) := by
  have hL := Nat.clog_pos (by decide : 1 < 2) (by omega : 1 < N)
  have hp := Nat.pow_pred_clog_lt_self (by decide : 1 < 2) (by omega : 1 < N)
  have hpow : (2 : ℝ) ^ (Nat.clog 2 N - 1) < (N : ℝ) := by exact_mod_cast hp
  apply (Real.le_logb_iff_rpow_le (by norm_num : (1 : ℝ) < 2) (by positivity)).mpr
  rw [show (Nat.clog 2 N : ℝ) + 1 = ((Nat.clog 2 N + 1 : ℕ) : ℝ) by push_cast; rfl,
    Real.rpow_natCast,
    show Nat.clog 2 N + 1 = (Nat.clog 2 N - 1) + 2 by omega, pow_add]
  norm_num
  linarith

/-- The genuine dyadic rank-one cost, plus the diagonal tensor cost, is bounded
by the exact constant ten printed in the flat-profile proposition.
Article: main_krylov, apG:flat. -/
theorem flat_dyadic_cost_log_bound {N : ℕ} (hN : 2 ≤ N) :
    2 * (Nat.clog 2 N : ℝ) * (2 : ℝ) ^ Nat.clog 2 N / (Real.sqrt 2 - 1) + N ≤
      10 * N * Real.logb 2 (4 * N) := by
  have hN0 : 0 ≤ (N : ℝ) := Nat.cast_nonneg _
  have hL0 : 0 ≤ (Nat.clog 2 N : ℝ) := Nat.cast_nonneg _
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hs0 := Real.sqrt_nonneg (2 : ℝ)
  have hs1 : 0 < Real.sqrt 2 - 1 := by nlinarith
  have hnum : 4 / (Real.sqrt 2 - 1) ≤ (10 : ℝ) := by
    apply (div_le_iff₀ hs1).mpr
    nlinarith
  have hcover := (flat_dyadic_cover hN).2.le
  have hbound : 2 * (Nat.clog 2 N : ℝ) * (2 : ℝ) ^ Nat.clog 2 N /
      (Real.sqrt 2 - 1) ≤ 10 * N * (Nat.clog 2 N : ℝ) := by
    calc
      _ ≤ 2 * (Nat.clog 2 N : ℝ) * (2 * N) / (Real.sqrt 2 - 1) := by gcongr
      _ = (4 / (Real.sqrt 2 - 1)) * N * (Nat.clog 2 N : ℝ) := by ring
      _ ≤ 10 * N * (Nat.clog 2 N : ℝ) := by gcongr
  calc
    _ ≤ 10 * N * (Nat.clog 2 N : ℝ) + N := by gcongr
    _ ≤ 10 * N * ((Nat.clog 2 N : ℝ) + 1) := by nlinarith
    _ ≤ _ := mul_le_mul_of_nonneg_left (flat_dyadic_log_margin hN) (by positivity)

end
end krylov.Tensor
