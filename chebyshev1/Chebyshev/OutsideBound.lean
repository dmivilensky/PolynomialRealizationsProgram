import chebyshev1.Chebyshev.Normalization

/-!
Article: chebyshev1, Theorem 4.3.
Positivity of the static-shift remainder, without a Taylor-series axiom.
Use: `chebyshev1.chebyshev_tangent_lower` feeds
`chebyshev1.Realization.static_shift_attained` (All three Chebyshev drift expressions are
attained on the same physical example).
Proof chain: `chebyshev1.Realization.static_shift_attained` — chebyshev1, Theorem 4.3; All
insertion orders, partition bounds, finite/cosh bounds and attainment.
-/
namespace chebyshev1
noncomputable section
open Polynomial Polynomial.Chebyshev

/--
The stated quantitative bound `(2 * (n : ℝ) + 1) * u ≤ (T ℝ (n + 1)).eval (1 + u) - (T ℝ
n).eval (1 + u)`.

Use: `chebyshev1.chebyshev_tangent_lower` uses this bound to establish the stated
quantitative bound `1 + (n : ℝ) ^ 2 * u ≤ (T ℝ n).eval (1 + u)`.

Article: chebyshev1, Corollary 4.4 via `chebyshev1.Prefix.static_shift_attained`.

Proof: Induct on `n`; the recursive step uses the previous-stage assertion.
-/
theorem chebyshev_increment_lower (n : ℕ) (u : ℝ) (hu : 0 ≤ u) :
    (2 * (n : ℝ) + 1) * u ≤ (T ℝ (n + 1)).eval (1 + u) - (T ℝ n).eval (1 + u) := by
  -- Induct on `n`; the recursive step uses the previous-stage assertion.
  induction n with
  | zero => simp
  | succ n ih =>
    have hc : (T ℝ (n + 2)).eval (1 + u) =
        2 * (1 + u) * (T ℝ (n + 1)).eval (1 + u) - (T ℝ n).eval (1 + u) := by
      simp [T_add_two]
    have hT := one_le_eval_T_real (n + 1) (show 1 ≤ 1 + u by linarith)
    have hp := mul_le_mul_of_nonneg_left hT hu
    push_cast
    rw [show (n : ℤ) + 1 + 1 = n + 2 by omega]
    rw [hc]
    nlinarith

/--
Positivity of the static-shift remainder, without a Taylor-series axiom.

The stated quantitative bound `1 + (n : ℝ) ^ 2 * u ≤ (T ℝ n).eval (1 + u)`.

Use: `chebyshev1.Realization.static_shift_attained` uses this bound to establish the
identity stated in that declaration.

Article: chebyshev1, Corollary 4.4 via `chebyshev1.Prefix.static_shift_attained`.

Proof: Induct on `n`; the recursive step uses the previous-stage assertion.
-/
theorem chebyshev_tangent_lower (n : ℕ) (u : ℝ) (hu : 0 ≤ u) :
    1 + (n : ℝ) ^ 2 * u ≤ (T ℝ n).eval (1 + u) := by
  -- Induct on `n`; the recursive step uses the previous-stage assertion.
  induction n with
  | zero => simp
  | succ n ih =>
    have hi := chebyshev_increment_lower n u hu
    push_cast
    nlinarith

end
end chebyshev1
