import chebyshev1.Prefix.Exactness

/-!
Article: chebyshev1, Theorem 2.2.
The remaining kernel formula of Theorem 2.2, for every valid insertion time.
Use: `chebyshev1.Prefix.kernel_succ` feeds `chebyshev1.Prefix.kernel_abs_le_endpoint`
(kernel abs le endpoint).
-/
namespace chebyshev1.Prefix

noncomputable section
open Polynomial Polynomial.Chebyshev
open scoped Matrix BigOperators

variable (I : SpectralInterval)

/--
Both coordinates of the tail fundamental solution, including the empty tail.

The precise assertion is `let M`.

Use: `chebyshev1.Prefix.tail_fundamental` uses this assertion to establish the identity
`orderedProduct (fun i => (realization I).scalarStep (r + i) lam) (N - r) 0 0 = I.den r / I.den
N * (U ℝ (N - r)).eval (I.z lam)`.

Article: chebyshev1, Theorem 2.2 via `chebyshev1.Prefix.kernel_zero`.

Proof: Induct on `k`; the recursive step uses the previous-stage assertion. Clear the
denominators using the available nonzero hypotheses, then verify the remaining algebraic
identity.
-/
theorem tail_column (r k : ℕ) (hr : 1 ≤ r) (lam : ℝ) :
    let M := orderedProduct (fun i => (realization I).scalarStep (r + i) lam) k
    M 0 0 = I.den r / I.den (r + k) * (U ℝ k).eval (I.z lam) ∧
    M 1 0 = I.den r / I.den (r + k - 1) *
      (U ℝ ((k : ℤ) - 1)).eval (I.z lam) := by
  -- Induct on `k`; the recursive step uses the previous-stage assertion.
  induction k with
  | zero => simp [orderedProduct, I.den_ne, U_neg_one]
  | succ k ih =>
    dsimp only at ih ⊢
    rw [orderedProduct_succ]
    have ht : r + k = (r + k - 1) + 1 := by omega
    rw [ht, scalarStep_succ]
    have hnext : r + k - 1 + 2 = r + (k + 1) := by omega
    have hcur : r + k - 1 + 1 = r + k := by omega
    simp only [hnext, hcur]
    constructor
    · simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, ih.1, ih.2]
      have hc : (U ℝ ((k : ℤ) + 1)).eval (I.z lam) =
          2 * I.z lam * (U ℝ k).eval (I.z lam) -
            (U ℝ ((k : ℤ) - 1)).eval (I.z lam) := by
        rw [U_add_one]
        simp
      push_cast
      field_simp [I.den_ne (r + k), I.den_ne (r + k - 1), I.den_ne (r + (k + 1))]
      rw [hc]
      ring
    · simpa [Matrix.mul_apply, Fin.sum_univ_two] using ih.1

/--
Lemma B.1, expressed as the actual ordered matrix tail.

Exact identity `orderedProduct (fun i => (realization I).scalarStep (r + i) lam) (N - r) 0 0 =
I.den r / I.den N * (U ℝ (N - r)).eval (I.z lam)`.

Use: `chebyshev1.Prefix.kernel_succ` rewrites with this identity to establish exact
identity `(realization I).kernel N (s + 1) lam nu = -(4 / (I.delta * I.den N)) * (U ℝ (N - (s +
2))).eval (I.z lam) * (T ℝ (s + 1)).eval (I.z nu)`.

Article: chebyshev1, Theorem 2.2 via `chebyshev1.Prefix.kernel_zero`.

Proof: Use the identities/estimates `chebyshev1.Prefix.tail_column` with the arguments
shown in the proof.
-/
theorem tail_fundamental (N r : ℕ) (hr : 1 ≤ r) (hrN : r ≤ N) (lam : ℝ) :
    orderedProduct (fun i => (realization I).scalarStep (r + i) lam) (N - r) 0 0 =
      I.den r / I.den N * (U ℝ (N - r)).eval (I.z lam) := by simpa only [Nat.add_sub_of_le hrN, Nat.cast_sub hrN] using (tail_column I r (N - r) hr lam).1

/--
Exact identity `(realization I).kernel N s lam nu = -(orderedProduct (fun i => (realization
I).scalarStep (s + 1 + i) lam) (N - (s + 1)) 0 0 * gamma I s * (orderedProduct (fun i =>
(realization I).scalarStep i nu) s) 0 0)`.

Use: `chebyshev1.Prefix.kernel_succ` rewrites with this identity to establish exact
identity `(realization I).kernel N (s + 1) lam nu = -(4 / (I.delta * I.den N)) * (U ℝ (N - (s +
2))).eval (I.z lam) * (T ℝ (s + 1)).eval (I.z nu)`.

Article: chebyshev1, Theorem 2.2 via `chebyshev1.Prefix.kernel_zero`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem kernel_factorization (N s : ℕ) (lam nu : ℝ) :
    (realization I).kernel N s lam nu =
      -(orderedProduct (fun i => (realization I).scalarStep (s + 1 + i) lam)
          (N - (s + 1)) 0 0 * gamma I s *
        (orderedProduct (fun i => (realization I).scalarStep i nu) s) 0 0) := by simp [Realization.kernel, Matrix.mul_apply, Fin.sum_univ_two]

/--
The first formula of Theorem 2.2; the query spectrum drops out at time zero.

Exact identity `(realization I).kernel N 0 lam nu = -(2 / (I.delta * I.den N)) * (U ℝ (N -
1)).eval (I.z lam)`.

Use: `chebyshev1.Prefix.endpoint_square_sum` rewrites with this identity to establish exact
identity `(∑ s ∈ Finset.range (n + 1), ((realization I).kernel (n + 1) s I.mu I.mu) ^ 2) = (2 /
(I.delta * I.den (n + 1))) ^ 2 * shape (n + 1)`.

Article: chebyshev1, Theorem 2.2.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem kernel_zero (N : ℕ) (hN : 1 ≤ N) (lam nu : ℝ) :
    (realization I).kernel N 0 lam nu =
      -(2 / (I.delta * I.den N)) * (U ℝ (N - 1)).eval (I.z lam) := by
  rw [kernel_factorization, tail_fundamental I N 1 (by omega) hN]
  simp only [gamma, orderedProduct_zero, Matrix.one_apply_eq, mul_one, I.den_one]
  dsimp [SpectralInterval.eta]
  field_simp [I.den_ne N, ne_of_gt I.delta_pos, ne_of_gt I.sum_pos]

/--
The remaining kernel formula of Theorem 2.2, for every valid insertion time.

Exact identity `(realization I).kernel N (s + 1) lam nu = -(4 / (I.delta * I.den N)) * (U ℝ (N
- (s + 2))).eval (I.z lam) * (T ℝ (s + 1)).eval (I.z nu)`.

Use: `chebyshev1.Prefix.endpoint_square_sum` rewrites with this identity to establish exact
identity `(∑ s ∈ Finset.range (n + 1), ((realization I).kernel (n + 1) s I.mu I.mu) ^ 2) = (2 /
(I.delta * I.den (n + 1))) ^ 2 * shape (n + 1)`.

Article: chebyshev1, Theorem 2.2.

Proof: Clear the denominators using the available nonzero hypotheses, then verify the remaining
algebraic identity.
-/
theorem kernel_succ (N s : ℕ) (hs : s + 1 < N) (lam nu : ℝ) :
    (realization I).kernel N (s + 1) lam nu =
      -(4 / (I.delta * I.den N)) *
        (U ℝ (N - (s + 2))).eval (I.z lam) * (T ℝ (s + 1)).eval (I.z nu) := by
  -- Clear the denominators using the available nonzero hypotheses, then verify the remaining
  -- algebraic identity.
  rw [kernel_factorization, tail_fundamental I N (s + 1 + 1) (by omega) (by omega),
    (prefix_column I s nu).1]
  dsimp [gamma]
  have hi : s + 1 + 1 = s + 2 := by omega
  rw [hi]
  field_simp [I.den_ne (s + 2), I.den_ne (s + 1), I.den_ne N,
    ne_of_gt I.delta_pos]
  rw [show (s : ℤ) + 1 + 1 = s + 2 by omega]
  ring

end
end chebyshev1.Prefix
