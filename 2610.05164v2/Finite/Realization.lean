import «2610.05164v2».Finite.Horizon
import «2606.16671v2».Jacobi.Exactness

/-!
Article: 2610.05164v2, Theorem 2.1.
The forward coefficient formulas in Theorem 2.1, with a finite horizon.
Use: `«2610.05164v2».Jacobi.recurrence_terminal` feeds
`«2610.05164v2».SineJacobi.symmetric_gain_exact` (symmetric gain exact).
Proof chain: `«2610.05164v2».recurrenceEquiv` — 2610.05164v2, Theorem 2.1; Bijection with all
admissible Jacobi matrices, including reducible matrices.
-/
namespace «2610.05164v2».Jacobi
noncomputable section
open «2606.16671v2»
variable {N : ℕ} (J : Jacobi N) (I : SpectralInterval)

/--
The forward coefficient formulas in Theorem 2.1, with a finite horizon.

Use: `«2610.05164v2».Jacobi.recurrence_agree` uses this definition to establish the precise
assertion is `Horizon.Agree N (J.recurrence I h).method (J.data.method I)`.

Article: 2610.05164v2, Theorem 2.1.
-/
def recurrence (h : J.data.Admissible I N) : Recurrence N where
  method := Horizon.truncate N (J.data.method I)
  normalized i := by
    by_cases hi : i < N
    · simp only [Horizon.truncate, hi, ite_true]
      cases i with
      | zero =>
        simp only [JacobiData.method, JacobiData.den_zero,
          J.coupling_zero, zero_mul, zero_div, neg_zero, add_zero]
        rw [Nat.zero_add, JacobiData.den_one]
        simpa [div_eq_mul_inv] using inv_mul_cancel₀
          (show I.eta-J.data.b 0 ≠ 0 by simpa using (h 1 (by omega)).ne')
      | succ i => exact J.data.fixed_point I i (h (i+2) (by omega)).ne'
    · simp [Horizon.truncate, hi]
  gamma_pos i := by
    by_cases hi : i < N
    · simp only [Horizon.truncate, hi, ite_true, JacobiData.method]
      exact div_pos (mul_pos (div_pos (by norm_num) I.delta_pos) (h i (by omega)))
        (h (i+1) (by omega))
    · simp [Horizon.truncate, hi]
  memory_nonpos i := by
    by_cases hi : i < N
    · simp only [Horizon.truncate, hi, ite_true, JacobiData.method]
      exact neg_nonpos.mpr (div_nonneg (mul_nonneg (J.coupling_nonneg i)
        (h (i-1) (by omega)).le) (h (i+1) (by omega)).le)
    · simp [Horizon.truncate, hi]
  memory_zero := by simp [Horizon.truncate, JacobiData.method, J.coupling_zero]
  alpha_tail i hi := by simp [Horizon.truncate, Nat.not_lt.mpr hi]
  memory_tail i hi := by simp [Horizon.truncate, Nat.not_lt.mpr hi]
  gamma_tail i hi := by simp [Horizon.truncate, Nat.not_lt.mpr hi]

/--
The precise assertion is `Horizon.Agree N (J.recurrence I h).method (J.data.method I)`.

Use: `«2610.05164v2».Jacobi.residual_eq` rewrites with this assertion to establish exact
identity `(J.recurrence I h).method.realization.residualPolynomial n = J.data.residual I n`.

Article: 2610.05164v2, Theorem 2.5 via `«2610.05164v2».SineJacobi.gain_exact`.

Proof: Use the identities/estimates `«2610.05164v2».Horizon.truncate_agree` with the arguments
shown in the proof.
-/
theorem recurrence_agree (h : J.data.Admissible I N) :
    Horizon.Agree N (J.recurrence I h).method (J.data.method I) :=
  Horizon.truncate_agree N (J.data.method I)

/--
Exact identity `(J.recurrence I h).method.realization.residualPolynomial n = J.data.residual I
n`.

Use: `«2610.05164v2».Jacobi.recurrence_terminal` rewrites with this identity to establish the
precise assertion is `(J.recurrence I (J.admissible I hN ht)).Terminal I`.

Article: 2610.05164v2, Theorem 2.1.

Proof: Use the identities/estimates `«2610.05164v2».Horizon.residual_eq`,
`«2610.05164v2».Jacobi.recurrence_agree`, `«2606.16671v2».JacobiData.residualPolynomial_eq`
with the arguments shown in the proof.
-/
theorem residual_eq (h : J.data.Admissible I N) {n : ℕ} (hn : n ≤ N) :
    (J.recurrence I h).method.realization.residualPolynomial n = J.data.residual I n := by
  rw [Horizon.residual_eq (J.recurrence_agree I h) hn]
  exact J.data.residualPolynomial_eq I h n hn

/--
The precise assertion is `(J.recurrence I (J.admissible I hN ht)).Terminal I`.

Use: `«2610.05164v2».recurrenceEquiv` uses this assertion in the displayed construction of
`recurrenceEquiv`. Its inputs and component formulas are fixed by that definition.

Article: 2610.05164v2, Theorem 2.1 via `«2610.05164v2».recurrenceEquiv`.

Proof: Use the identities/estimates `«2610.05164v2».Jacobi.admissible`,
`«2610.05164v2».Jacobi.residual_eq`, `«2606.16671v2».JacobiData.terminal_residual` with the
arguments shown in the proof.
-/
theorem recurrence_terminal (hN : 0 < N) (ht : J.Terminal) :
    (J.recurrence I (J.admissible I hN ht)).Terminal I := by
  rw [Recurrence.Terminal, J.residual_eq I (J.admissible I hN ht) le_rfl]
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
  exact J.data.terminal_residual I (pow_ne_zero n (by norm_num))
    (ht.trans (fiberPolynomial_succ n))

end
end «2610.05164v2».Jacobi
