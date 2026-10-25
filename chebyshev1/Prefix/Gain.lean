import chebyshev1.Prefix.Kernel
import chebyshev1.Realization.Gain

/-!
Article: chebyshev1, Theorem 2.2.
The unevaluated square-sum formula in Theorem 2.2 (the zero term is harmless).
Use: `chebyshev1.Prefix.gain_exact_sum` feeds `chebyshev1.TwoTerm.optimal_gain` (Theorem
3.1: every recurrence in the class has the same exact optimal value).
-/
namespace chebyshev1.Prefix
noncomputable section
open Polynomial Polynomial.Chebyshev
open scoped BigOperators
variable (I : SpectralInterval)

/--
The stated quantitative bound `|(realization I).kernel N s lam nu| ≤ |(realization I).kernel N
s I.mu I.mu|`.

Use: `chebyshev1.Prefix.kernelNorm_le_endpoint` uses this bound to establish the stated
quantitative bound `(realization I).kernelNorm N lam nu ≤ (realization I).kernelNorm N I.mu
I.mu`.

Article: chebyshev1, Theorem 2.2 via `chebyshev1.Prefix.gain_exact`.

Proof: Use the identities/estimates `chebyshev1.SpectralInterval.z_mem`,
`chebyshev1.Prefix.kernel_zero`, `chebyshev1.SpectralInterval.z_mu` with the arguments
shown in the proof.
-/
theorem kernel_abs_le_endpoint (N s : ℕ) (hs : s < N) {lam nu : ℝ}
    (hl : lam ∈ Set.Icc I.mu I.L) (hn : nu ∈ Set.Icc I.mu I.L) :
    |(realization I).kernel N s lam nu| ≤ |(realization I).kernel N s I.mu I.mu| := by
  -- Use the identities/estimates `chebyshev1.SpectralInterval.z_mem`,
  -- `chebyshev1.Prefix.kernel_zero`, `chebyshev1.SpectralInterval.z_mu` with the
  -- arguments shown in the proof.
  have hz := abs_le.mpr (I.z_mem hl)
  have hy := abs_le.mpr (I.z_mem hn)
  cases s with
  | zero =>
    rw [kernel_zero I N (by omega), kernel_zero I N (by omega)]
    simp only [I.z_mu, U_eval_one, abs_mul]
    have hindex : (N : ℤ) - 1 = ((N - 1 : ℕ) : ℤ) := by omega
    rw [hindex]
    have hu := abs_U_eval_le (N - 1) hz
    push_cast
    have hh : (0 : ℝ) ≤ (N - 1 : ℕ) + 1 := by positivity
    rw [abs_of_nonneg hh]
    exact mul_le_mul_of_nonneg_left hu (abs_nonneg _)
  | succ s =>
    rw [kernel_succ I N s hs, kernel_succ I N s hs]
    simp only [I.z_mu, U_eval_one, T_eval_one, mul_one, abs_mul]
    have hindex : (N : ℤ) - (s + 2) = ((N - (s + 2) : ℕ) : ℤ) := by omega
    rw [hindex]
    have hu := abs_U_eval_le (N - (s + 2)) hz
    have ht := abs_eval_T_real_le_one (s + 1) hy
    push_cast
    have hh : (0 : ℝ) ≤ (N - (s + 2) : ℕ) + 1 := by positivity
    rw [abs_of_nonneg hh]
    calc
      _ ≤ |-(4 / (I.delta * I.den N))| * |(U ℝ ((N - (s + 2) : ℕ) : ℤ)).eval (I.z lam)| * 1 :=
        mul_le_mul_of_nonneg_left ht (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      _ ≤ _ := by simpa using mul_le_mul_of_nonneg_left hu (abs_nonneg (-(4 / (I.delta * I.den N))))

/--
The stated quantitative bound `(realization I).kernelNorm N lam nu ≤ (realization I).kernelNorm
N I.mu I.mu`.

Use: `chebyshev1.Prefix.gain_isGreatest` uses this bound to establish the precise assertion
is `IsGreatest ((realization I).gainValues I N) ((realization I).kernelNorm N I.mu I.mu)`.

Article: chebyshev1, Theorem 2.2 via `chebyshev1.Prefix.gain_exact`.

Proof: Use the identities/estimates `chebyshev1.Prefix.kernel_abs_le_endpoint` with the
arguments shown in the proof.
-/
theorem kernelNorm_le_endpoint (N : ℕ) {lam nu : ℝ}
    (hl : lam ∈ Set.Icc I.mu I.L) (hn : nu ∈ Set.Icc I.mu I.L) :
    (realization I).kernelNorm N lam nu ≤ (realization I).kernelNorm N I.mu I.mu := by
  apply Real.sqrt_le_sqrt
  apply Finset.sum_le_sum
  intro s hs
  exact sq_le_sq.mpr (kernel_abs_le_endpoint I N s (Finset.mem_range.mp hs) hl hn)

/--
The two parameters attain their maximum simultaneously at the left endpoint.

The precise assertion is `IsGreatest ((realization I).gainValues I N) ((realization
I).kernelNorm N I.mu I.mu)`.

Use: `chebyshev1.Prefix.gain_eq_endpoint` uses this assertion to establish the identity
`(realization I).gain I N = (realization I).kernelNorm N I.mu I.mu`.

Article: chebyshev1, Theorem 2.2 via `chebyshev1.Prefix.gain_exact`.

Proof: Use the identities/estimates `chebyshev1.Prefix.kernelNorm_le_endpoint` with the
arguments shown in the proof.
-/
theorem gain_isGreatest (N : ℕ) :
    IsGreatest ((realization I).gainValues I N) ((realization I).kernelNorm N I.mu I.mu) := by
  constructor
  · exact ⟨I.mu, ⟨le_rfl, I.mu_lt_L.le⟩, I.mu, ⟨le_rfl, I.mu_lt_L.le⟩, rfl⟩
  · rintro v ⟨lam, hl, nu, hn, rfl⟩
    exact kernelNorm_le_endpoint I N hl hn

/--
Exact identity `(realization I).gain I N = (realization I).kernelNorm N I.mu I.mu`.

Use: `chebyshev1.Prefix.gain_exact` rewrites with this identity to establish the identity
`(realization I).gain I N = 2 * I.epsilon N / I.delta * Real.sqrt (shape N)`.

Article: chebyshev1, Theorem 2.2 via `chebyshev1.Prefix.gain_exact`.

Proof: Use the identities/estimates `chebyshev1.Prefix.gain_isGreatest` with the arguments
shown in the proof.
-/
theorem gain_eq_endpoint (N : ℕ) :
    (realization I).gain I N = (realization I).kernelNorm N I.mu I.mu :=
  (gain_isGreatest I N).isLUB.csSup_eq ⟨_, (gain_isGreatest I N).1⟩

/--
The finite sum used in the exact gain calculation, in reversed time order.

Exact identity `(∑ s ∈ Finset.range n, ((n : ℝ) - s) ^ 2) = (n : ℝ) * (n + 1) * (2 * n + 1) /
6`.

Use: `chebyshev1.Prefix.endpoint_square_sum` rewrites with this identity to establish exact
identity `(∑ s ∈ Finset.range (n + 1), ((realization I).kernel (n + 1) s I.mu I.mu) ^ 2) = (2 /
(I.delta * I.den (n + 1))) ^ 2 * shape (n + 1)`.

Article: chebyshev1, Theorem 2.2 via `chebyshev1.Prefix.gain_exact`.

Proof: Induct on `n`; the recursive step uses the previous-stage assertion.
-/
theorem reversed_square_sum (n : ℕ) :
    (∑ s ∈ Finset.range n, ((n : ℝ) - s) ^ 2) =
      (n : ℝ) * (n + 1) * (2 * n + 1) / 6 := by
  -- Induct on `n`; the recursive step uses the previous-stage assertion.
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ']
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, sub_zero]
    have hshift (s : ℕ) : ((n : ℝ) + 1 - (s + 1)) ^ 2 = ((n : ℝ) - s) ^ 2 := by ring
    simp_rw [hshift]
    rw [ih]
    ring

/--
Defines `shape` of type `ℝ` by `(N : ℝ) ^ 2 + (2 / 3 : ℝ) * N * (N - 1) * (2 * N - 1)`.

Use: `chebyshev1.Prefix.endpoint_square_sum` uses this definition to establish exact
identity `(∑ s ∈ Finset.range (n + 1), ((realization I).kernel (n + 1) s I.mu I.mu) ^ 2) = (2 /
(I.delta * I.den (n + 1))) ^ 2 * shape (n + 1)`.

Article: chebyshev1, Theorem 2.2 via `chebyshev1.Prefix.gain_exact`.
-/
def shape (N : ℕ) : ℝ :=
  (N : ℝ) ^ 2 + (2 / 3 : ℝ) * N * (N - 1) * (2 * N - 1)

/--
Exact identity `(∑ s ∈ Finset.range (n + 1), ((realization I).kernel (n + 1) s I.mu I.mu) ^ 2)
= (2 / (I.delta * I.den (n + 1))) ^ 2 * shape (n + 1)`.

Use: `chebyshev1.Prefix.gain_exact` rewrites with this identity to establish the identity
`(realization I).gain I N = 2 * I.epsilon N / I.delta * Real.sqrt (shape N)`.

Article: chebyshev1, Theorem 2.2 via `chebyshev1.Prefix.gain_exact`.

Proof: Identify the summands/integrands on their required domain before replacing the sum or
integral.
-/
theorem endpoint_square_sum (n : ℕ) :
    (∑ s ∈ Finset.range (n + 1), ((realization I).kernel (n + 1) s I.mu I.mu) ^ 2) =
      (2 / (I.delta * I.den (n + 1))) ^ 2 * shape (n + 1) := by
  -- Identify the summands/integrands on their required domain before replacing the sum or
  -- integral.
  rw [Finset.sum_range_succ']
  have hterm (s : ℕ) (hs : s ∈ Finset.range n) :
      ((realization I).kernel (n + 1) (s + 1) I.mu I.mu) ^ 2 =
        (4 / (I.delta * I.den (n + 1))) ^ 2 * ((n : ℝ) - s) ^ 2 := by
    rw [kernel_succ I (n + 1) s (by have := Finset.mem_range.mp hs; omega)]
    simp only [I.z_mu, U_eval_one, T_eval_one, mul_one]
    push_cast
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, reversed_square_sum,
    kernel_zero I (n + 1) (by omega)]
  simp only [I.z_mu, U_eval_one]
  dsimp [shape]
  push_cast
  ring

/--
The exact finite formula in Theorem 2.2, with the square sum evaluated.

Exact identity `(realization I).gain I N = 2 * I.epsilon N / I.delta * Real.sqrt (shape N)`.

Use: `chebyshev1.Prefix.gain_exact_sum` rewrites with this identity to establish exact
identity `(realization I).gain I N = I.epsilon N / I.delta * Real.sqrt (4 * (N : ℝ) ^ 2 + 16 *
∑ m ∈ Finset.range N, (m : ℝ) ^ 2)`.

Article: chebyshev1, Theorem 2.2.

Proof: Use the identities/estimates `chebyshev1.Prefix.gain_eq_endpoint`,
`chebyshev1.Prefix.endpoint_square_sum`, `chebyshev1.SpectralInterval.delta_pos` with
the arguments shown in the proof.
-/
theorem gain_exact (N : ℕ) (hN : 1 ≤ N) :
    (realization I).gain I N =
      2 * I.epsilon N / I.delta * Real.sqrt (shape N) := by
  -- Use the identities/estimates `chebyshev1.Prefix.gain_eq_endpoint`,
  -- `chebyshev1.Prefix.endpoint_square_sum`, `chebyshev1.SpectralInterval.delta_pos`
  -- with the arguments shown in the proof.
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : N ≠ 0)
  rw [gain_eq_endpoint, Realization.kernelNorm, endpoint_square_sum, Real.sqrt_mul
    (sq_nonneg _), Real.sqrt_sq_eq_abs, abs_of_pos (div_pos (by norm_num) (mul_pos I.delta_pos (I.den_pos _)))]
  dsimp [SpectralInterval.epsilon]
  ring

/--
Exact identity `(∑ m ∈ Finset.range N, (m : ℝ) ^ 2) = (N : ℝ) * (N - 1) * (2 * N - 1) / 6`.

Use: `chebyshev1.Prefix.gain_exact_sum` rewrites with this identity to establish exact
identity `(realization I).gain I N = I.epsilon N / I.delta * Real.sqrt (4 * (N : ℝ) ^ 2 + 16 *
∑ m ∈ Finset.range N, (m : ℝ) ^ 2)`.

Article: chebyshev1, Theorem 2.2 via `chebyshev1.Prefix.gain_exact_sum`.

Proof: Induct on `N`; the recursive step uses the previous-stage assertion.
-/
theorem square_sum (N : ℕ) :
    (∑ m ∈ Finset.range N, (m : ℝ) ^ 2) = (N : ℝ) * (N - 1) * (2 * N - 1) / 6 := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

/--
The unevaluated square-sum formula in Theorem 2.2 (the zero term is harmless).

Exact identity `(realization I).gain I N = I.epsilon N / I.delta * Real.sqrt (4 * (N : ℝ) ^ 2 +
16 * ∑ m ∈ Finset.range N, (m : ℝ) ^ 2)`.

Use: `chebyshev1.TwoTerm.optimal_gain` rewrites with this identity to establish exact
identity `S.realization.gain I N = I.epsilon N / I.delta * Real.sqrt (4 * (N : ℝ) ^ 2 + 16 * ∑
m ∈ Finset.range N, (m : ℝ) ^ 2)`.

Article: chebyshev1, Theorem 2.2.

Proof: Use the identities/estimates `chebyshev1.Prefix.gain_exact`,
`chebyshev1.Prefix.square_sum` with the arguments shown in the proof.
-/
theorem gain_exact_sum (N : ℕ) (hN : 1 ≤ N) :
    (realization I).gain I N = I.epsilon N / I.delta *
      Real.sqrt (4 * (N : ℝ) ^ 2 + 16 * ∑ m ∈ Finset.range N, (m : ℝ) ^ 2) := by
  -- Use the identities/estimates `chebyshev1.Prefix.gain_exact`,
  -- `chebyshev1.Prefix.square_sum` with the arguments shown in the proof.
  rw [gain_exact I N hN, square_sum]
  have hshape : 4 * (N : ℝ) ^ 2 + 16 * ((N : ℝ) * (N - 1) * (2 * N - 1) / 6) =
      4 * shape N := by dsimp [shape]; ring
  rw [hshape, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
  norm_num
  ring

end
end chebyshev1.Prefix
