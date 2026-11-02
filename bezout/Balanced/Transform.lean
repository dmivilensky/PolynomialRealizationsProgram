import bezout.Balanced.Basis

/-!
Article: bezout, positive parity factorization in the proof of Theorem `thm:linear`.
Use: a finite exact change of basis converts parity-tail factors into the
stopped-parity basis. The statement is pointwise and includes the diagonal.
Proof: two-step telescoping, with both terminal terms proved zero.
-/

namespace bezout.Balanced
noncomputable section
open Polynomial Polynomial.Chebyshev
open scoped BigOperators

/-- Two-step finite telescoping retains exactly the two parity boundary terms. -/
theorem sum_stride_two (n : ℕ) (f : ℕ → ℝ) :
    ∑ s ∈ Finset.range n, (f s - f (s + 2)) =
      f 0 + f 1 - f n - f (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih]; ring

/-- Exact conversion of arbitrary finite parity tails to the Balanced basis. -/
theorem parity_transform (N : ℕ) (hN : 2 ≤ N) (R : ℕ → ℝ)
    (hR : ∀ s, N ≤ s → R s = 0) (x : ℝ) :
    (∑ s ∈ Finset.range N,
      (R s / omega N s - R (s + 2) / omega N (s + 2)) * (psi N s).eval x) =
    ∑ s ∈ Finset.range N, (R s - R (s + 2)) * (T ℝ s).eval x := by
  let E (s : ℕ) := R s / omega N s * (psi N s).eval x - R s * (T ℝ s).eval x
  have hzero : E 0 = 0 := by simp [E]
  have hone : E 1 = 0 := by simp [E]
  have hterminal : E N = 0 := by simp [E, hR N le_rfl]
  have hterminal' : E (N + 1) = 0 := by simp [E, hR (N + 1) (by omega)]
  have hlocal (s : ℕ) (hs : s < N) :
      (R s / omega N s - R (s + 2) / omega N (s + 2)) * (psi N s).eval x -
        (R s - R (s + 2)) * (T ℝ s).eval x = E s - E (s + 2) := by
    by_cases ht : s + 2 < N
    · have hw := ne_of_gt (omega_pos hN ht)
      have hp := congrArg (fun p : ℝ[X] => p.eval x) (psi_add_two N s)
      simp only [eval_add, eval_mul, eval_C, eval_sub] at hp
      dsimp [E]
      rw [hp]
      field_simp
      ring
    · have hz := hR (s + 2) (by omega)
      simp [E, hz]
  have hsum := sum_stride_two N E
  rw [hzero, hone, hterminal, hterminal'] at hsum
  apply sub_eq_zero.mp
  rw [← Finset.sum_sub_distrib]
  convert hsum using 1
  · apply Finset.sum_congr rfl
    intro s hs
    exact hlocal s (Finset.mem_range.mp hs)
  · ring

end
end bezout.Balanced
