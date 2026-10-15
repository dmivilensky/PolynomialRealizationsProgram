import «2606.16671v2».Algebra.Continuant
import «2606.16671v2».SineJacobi.Reversal

/-!
Article: 2606.16671v2, Lemma E.8.
The encoding evaluates to the actual continuant, including every interior block.
Use: `«2606.16671v2».SineJacobi.blockFourier_cosine` feeds `«2606.16671v2».SineJacobi.block_fourier`
(block fourier).
Proof chain: `«2606.16671v2».SineJacobi.endpointMax` — 2606.16671v2, Lemma E.8; Nonnegative Fourier
coefficients and endpoint maxima for every block.
-/
namespace «2606.16671v2».SineJacobi
noncomputable section
open Polynomial Real
open scoped BigOperators

/--
Polynomial encoding all cosine modes of an arbitrary sine-chain block.

Use: `«2606.16671v2».SineJacobi.blockFourier_tail` uses this definition to establish exact
identity `blockFourier N (N-n) n = blockFourier N 0 n`.

Article: 2606.16671v2, Corollary 5.3 via `«2606.16671v2».SineJacobi.G_exact`.
-/
def blockFourier (N a n : ℕ) : ℝ[X] :=
  Continuant.continuant (fun _ => 1+X) (fun s => C (4*(data N).aSq s)*X) a n

/--
Exact identity `blockFourier N a 0 = 1`.

Use: registered as a simplification rule for the displayed expression. The rule remains
available even when kernel reduction eliminates an explicit reference to this lemma.

Article: 2606.16671v2, Lemma E.8.

Proof: The identity follows by unfolding the definitions; no estimate or limiting argument is
involved.
-/
@[simp] theorem blockFourier_zero (N a : ℕ) : blockFourier N a 0 = 1 := rfl
/--
Exact identity `blockFourier N a 1 = 1+X`.

Use: registered as a simplification rule for the displayed expression. The rule remains
available even when kernel reduction eliminates an explicit reference to this lemma.

Article: 2606.16671v2, Lemma E.8.

Proof: The identity follows by unfolding the definitions; no estimate or limiting argument is
involved.
-/
@[simp] theorem blockFourier_one (N a : ℕ) : blockFourier N a 1 = 1+X := rfl

/--
Exact identity `blockFourier N a (n+2) = (1+X)*blockFourier N a (n+1) - C (4*(data N).aSq
(a+n+1))*X*blockFourier N a n`.

Use: `«2606.16671v2».SineJacobi.blockFourier_cosine` rewrites with this identity to establish
exact identity `(2:ℝ)^n*((data N).block a n).eval (cos theta) = cosineTransform (n:ℤ) theta
(blockFourier N a n)`.

Article: 2606.16671v2, Corollary 5.3 via `«2606.16671v2».SineJacobi.G_exact`.

Proof: The identity follows by unfolding the definitions; no estimate or limiting argument is
involved.
-/
theorem blockFourier_rec (N a n : ℕ) :
    blockFourier N a (n+2) = (1+X)*blockFourier N a (n+1) -
      C (4*(data N).aSq (a+n+1))*X*blockFourier N a n := rfl

/--
The stated quantitative bound `(blockFourier N a n).natDegree ≤ n`.

Use: `«2606.16671v2».SineJacobi.blockFourier_interior_nonneg` uses this bound to establish the
stated quantitative bound `0 ≤ (blockFourier N a n).coeff k`.

Article: 2606.16671v2, Corollary 5.3 via `«2606.16671v2».SineJacobi.G_exact`.

Proof: Induct on `n`; the recursive step uses the previous-stage assertion.
-/
theorem blockFourier_degree (N a n : ℕ) : (blockFourier N a n).natDegree ≤ n := by
  -- Induct on `n`; the recursive step uses the previous-stage assertion.
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n h0 h1 =>
    rw [blockFourier_rec]
    refine le_trans (natDegree_sub_le_of_le (m := n+2) (n := n+2) ?_ ?_) (by simp)
    · have hh : (1+X : ℝ[X]).natDegree ≤ 1 := by compute_degree
      exact natDegree_mul_le.trans (by omega)
    · have hh : (C (4*(data N).aSq (a+n+1))*X : ℝ[X]).natDegree ≤ 1 := by compute_degree
      exact natDegree_mul_le.trans (by omega)

/--
Exact identity `blockFourier N 0 s = rogers N s`.

Use: `«2606.16671v2».SineJacobi.blockFourier_terminal` rewrites with this identity to establish
exact identity `blockFourier N 0 N = 1+X^N`.

Article: 2606.16671v2, Corollary 5.3 via `«2606.16671v2».SineJacobi.G_exact`.

Proof: Induct on `s`; the recursive step uses the previous-stage assertion.
-/
theorem blockFourier_leading (N s : ℕ) (hs : s < N) : blockFourier N 0 s = rogers N s := by
  -- Induct on `s`; the recursive step uses the previous-stage assertion.
  induction s using Nat.twoStepInduction with
  | zero => exact (rogers_zero N (by omega)).symm
  | one => exact (rogers_one N hs).symm
  | more s h0 h1 =>
    rw [blockFourier_rec, h1 (by omega), h0 (by omega)]
    rw [show s+2 = (s+1)+1 by omega, rogers_recurrence N (s+1) hs (by omega)]
    simp only [Nat.zero_add, Nat.add_sub_cancel]
    rw [data_aSq N (s+1) (by omega) (by omega)]

/--
Exact identity `blockFourier N 0 N = 1+X^N`.

Use: `«2606.16671v2».SineJacobi.blockFourier_interior_nonneg` rewrites with this identity to
establish the stated quantitative bound `0 ≤ (blockFourier N a n).coeff k`.

Article: 2606.16671v2, Corollary 5.3 via `«2606.16671v2».SineJacobi.G_exact`.

Proof: Separate `N = 1` from its negation; prove the goal under each of these mutually
exclusive hypotheses.
-/
theorem blockFourier_terminal (N : ℕ) (hN : 0 < N) : blockFourier N 0 N = 1+X^N := by
  -- Separate `N = 1` from its negation; prove the goal under each of these mutually exclusive
  -- hypotheses.
  by_cases h1 : N = 1
  · subst N; simp
  · have h2 : 2 ≤ N := by omega
    have hr := blockFourier_rec N 0 (N-2)
    rw [show N-2+2 = N by omega, show N-2+1 = N-1 by omega] at hr
    rw [hr, blockFourier_leading N (N-1) (by omega),
      blockFourier_leading N (N-2) (by omega)]
    simp only [Nat.zero_add]
    rw [show N-2+1 = N-1 by omega, data_aSq N (N-1) (by omega) (by omega)]
    exact rogers_terminal N h2

/--
Exact identity `blockFourier N (N-n) n = blockFourier N 0 n`.

Use: `«2606.16671v2».SineJacobi.blockFourier_tail_of_end` uses this identity to establish exact
identity `blockFourier N a n = blockFourier N 0 n`.

Article: 2606.16671v2, Corollary 5.3 via `«2606.16671v2».SineJacobi.G_exact`.

Proof: Induct on `n`; the recursive step uses the previous-stage assertion.
-/
theorem blockFourier_tail (N n : ℕ) (hn : n ≤ N) :
    blockFourier N (N-n) n = blockFourier N 0 n := by
  -- Induct on `n`; the recursive step uses the previous-stage assertion.
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n h0 h1 =>
    have hl := Continuant.block_left (fun _ => (1+X : ℝ[X]))
      (fun s => C (4*(data N).aSq s)*X) (N-(n+2)) n
    change blockFourier N (N-(n+2)) (n+2) = (1+X)*blockFourier N (N-(n+2)+1) (n+1) -
      C (4*(data N).aSq (N-(n+2)+1))*X*blockFourier N (N-(n+2)+2) n at hl
    rw [show N-(n+2)+1 = N-(n+1) by omega,
      show N-(n+2)+2 = N-n by omega, h1 (by omega), h0 (by omega)] at hl
    rw [show N-(n+1) = N-(n+1) by rfl, data_aSq_reflect N (n+1) (by omega)] at hl
    simpa only [blockFourier_rec, Nat.zero_add] using hl

/--
Exact identity `blockFourier N a n = blockFourier N 0 n`.

Use: `«2606.16671v2».SineJacobi.blockFourier_interior_nonneg` rewrites with this identity to
establish the stated quantitative bound `0 ≤ (blockFourier N a n).coeff k`.

Article: 2606.16671v2, Corollary 5.3 via `«2606.16671v2».SineJacobi.G_exact`.

Proof: Use the identities/estimates `«2606.16671v2».SineJacobi.blockFourier_tail` with the
arguments shown in the proof.
-/
theorem blockFourier_tail_of_end (N a n : ℕ) (ha : a+n = N) :
    blockFourier N a n = blockFourier N 0 n := by
  rw [show a = N-n by omega]
  exact blockFourier_tail N n (by omega)

/--
The encoding evaluates to the actual continuant, including every interior block.

Exact identity `(2:ℝ)^n*((data N).block a n).eval (cos theta) = cosineTransform (n:ℤ) theta
(blockFourier N a n)`.

Use: `«2606.16671v2».SineJacobi.block_fourier` rewrites with this identity to establish exact
identity `(2:ℝ)^n*((data N).block a n).eval (cos theta) = ∑ k ∈ Finset.range (n+1),
(blockFourier N a n).coeff k * cos (((n:ℝ)-2*(k:ℝ))*theta)`.

Article: 2606.16671v2, Corollary 5.3 via `«2606.16671v2».SineJacobi.G_exact`.

Proof: Induct on `n`; the recursive step uses the previous-stage assertion.
-/
theorem blockFourier_cosine (N a n : ℕ) (theta : ℝ) :
    (2:ℝ)^n*((data N).block a n).eval (cos theta) =
      cosineTransform (n:ℤ) theta (blockFourier N a n) := by
  -- Induct on `n`; the recursive step uses the previous-stage assertion.
  induction n using Nat.twoStepInduction with
  | zero => simp [JacobiData.block]
  | one =>
    simp [JacobiData.block, cosineTransform_X, cosineTransform_one]
    ring_nf
    simp
    ring
  | more n h0 h1 =>
    rw [blockFourier_rec, show ((n+2:ℕ):ℤ) = ((n+1:ℕ):ℤ)+1 by omega,
      cosineTransform_recurrence]
    rw [← h1, show ((n+1:ℕ):ℤ)-1 = (n:ℤ) by omega, ← h0]
    rw [JacobiData.block.eq_3 (data N) a n]
    simp only [data_b, C_0, sub_zero, eval_sub, eval_mul, eval_X, eval_C, pow_succ]
    ring

end
end «2606.16671v2».SineJacobi
