import bezout.Balanced.Factors

/-!
Article: bezout, finite reverse parity sums in Algorithm 2.
Use: finite tails are explicit arithmetic sums, including their endpoint masses.
Proof: extraction of the first parity term, followed by ordinary finite induction.
-/

namespace bezout.Balanced
noncomputable section
open Polynomial Polynomial.Chebyshev
open scoped BigOperators

/-- The number of surviving query degrees in the parity tail of a valid call. -/
def parityLength (N s : ℕ) : ℕ := (N - 1 - s) / 2 + 1

/-- A parity tail is exactly its finite forward sum of Hall coefficients. -/
theorem tail_range_aux (N m s : ℕ) (hterminal : N ≤ s + 2 * m)
    (hvalid : ∀ j < m, s + 2 * j < N) :
    tail N s = ∑ j ∈ Finset.range m, originalFactor N (s + 2 * j) := by
  induction m generalizing s with
  | zero => simpa using tail_eq_zero (by simpa using hterminal)
  | succ m ih =>
    have hs : s < N := by simpa using hvalid 0 (by omega)
    have ht : N ≤ (s + 2) + 2 * m := by omega
    have hv : ∀ j < m, (s + 2) + 2 * j < N := by
      intro j hj
      have hh := hvalid (j + 1) (by omega)
      omega
    have hr := tail_sub_add_two hs
    have hi := ih (s + 2) ht hv
    rw [Finset.sum_range_succ']
    have he : (∑ j ∈ Finset.range m, originalFactor N (s + 2 * (j + 1))) = tail N (s + 2) := by
      rw [hi]
      apply Finset.sum_congr rfl
      intro j _
      congr 1
      omega
    rw [he]
    simp only [mul_zero, add_zero]
    simpa only [add_comm] using sub_eq_iff_eq_add.mp hr

/-- The exact forward-sum form used to count nonnegative response terms. -/
theorem tail_range {N s : ℕ} (hs : s < N) :
    tail N s = ∑ j ∈ Finset.range (parityLength N s), originalFactor N (s + 2 * j) := by
  apply tail_range_aux
  · unfold parityLength
    omega
  · intro j hj
    unfold parityLength at hj
    omega

/-- Finite arithmetic-progression sum over the real numbers. -/
theorem sum_real_progression (m : ℕ) (A : ℝ) :
    ∑ j ∈ Finset.range m, (A - 2 * j) = (m : ℝ) * (A - m + 1) := by
  induction m with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

/-- The exact common-endpoint mass of a reverse parity sum. -/
theorem tail_eval_one {N s : ℕ} (hs : s < N) :
    (tail N s).eval 1 = (parityLength N s : ℝ) *
      ((N : ℝ) - s - parityLength N s + 1) - (if s = 0 then (N : ℝ) / 2 else 0) := by
  rw [tail_range hs, eval_finsetSum]
  have ht (j : ℕ) (hj : j < parityLength N s) : s + 2 * j < N := by
    unfold parityLength at hj
    omega
  have hv (j : ℕ) (hj : j < parityLength N s) :
      (originalFactor N (s + 2 * j)).eval 1 =
        (N : ℝ) - s - 2 * j - (if s = 0 ∧ j = 0 then (N : ℝ) / 2 else 0) := by
    have hlt := ht j hj
    simp only [originalFactor, eval_mul, eval_C, U_eval_one]
    push_cast
    have hc : ((N - 1 - (s + 2 * j) : ℕ) : ℝ) + 1 = (N : ℝ) - s - 2 * j := by
      have hh : N - 1 - (s + 2 * j) + 1 + s + 2 * j = N := by omega
      have hhr : ((N - 1 - (s + 2 * j) : ℕ) : ℝ) + 1 + s + 2 * j = N := by exact_mod_cast hh
      linarith
    rw [hc]
    by_cases hz : s = 0 ∧ j = 0
    · rcases hz with ⟨rfl, rfl⟩
      simp [hallWeight]
      ring
    · simp [hallWeight, hz]
  have hsum :
      (∑ j ∈ Finset.range (parityLength N s), (originalFactor N (s + 2 * j)).eval 1) =
      ∑ j ∈ Finset.range (parityLength N s),
        ((N : ℝ) - s - 2 * j - (if s = 0 ∧ j = 0 then (N : ℝ) / 2 else 0)) := by
    apply Finset.sum_congr rfl
    intro j hj
    exact hv j (Finset.mem_range.mp hj)
  rw [hsum, Finset.sum_sub_distrib, sum_real_progression]
  congr 1
  by_cases hz : s = 0
  · simp [hz, parityLength]
  · simp [hz]

end
end bezout.Balanced
