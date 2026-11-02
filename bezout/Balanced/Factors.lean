import bezout.Balanced.Transform
import bezout.Balanced.History
import bezout.Flat.Chebyshev

/-!
Article: bezout, Equations `eq:V` and `eq:stopped-readout`.
Use: exact polynomial responses obtained from finite reverse parity tails.
Proof: two-step telescoping followed by the complete Hall expansion.
-/

namespace bezout.Balanced
noncomputable section
open Polynomial Polynomial.Chebyshev
open scoped BigOperators

/-- Degree-zero carries the half weight in the original Hall expansion. -/
def hallWeight (s : ℕ) : ℝ := if s = 0 then 1 / 2 else 1

/-- The coefficient polynomial of a first-kind query in the Hall expansion. -/
def originalFactor (N s : ℕ) : ℝ[X] :=
  C (hallWeight s) * U ℝ ((N - 1 - s : ℕ) : ℤ)

/-- Finite reverse parity sum, zero after the last call. -/
def tail (N s : ℕ) : ℝ[X] :=
  ∑ t ∈ Finset.range N, if s ≤ t ∧ s % 2 = t % 2 then originalFactor N t else 0

/-- The reverse parity sum has zero terminal boundary values. -/
theorem tail_eq_zero {N s : ℕ} (hs : N ≤ s) : tail N s = 0 := by
  unfold tail
  apply Finset.sum_eq_zero
  intro t ht
  have ht' := Finset.mem_range.mp ht
  split_ifs with h
  · omega
  · rfl

/-- One parity-tail difference extracts exactly one Hall coefficient. -/
theorem tail_sub_add_two {N s : ℕ} (hs : s < N) :
    tail N s - tail N (s + 2) = originalFactor N s := by
  unfold tail
  rw [← Finset.sum_sub_distrib]
  calc
    _ = ∑ t ∈ Finset.range N, if t = s then originalFactor N s else 0 := by
      apply Finset.sum_congr rfl
      intro t _
      by_cases hts : t = s
      · subst t
        simp
      · have hp : (s + 2) % 2 = s % 2 := by omega
        by_cases h : s ≤ t ∧ s % 2 = t % 2
        · have h' : s + 2 ≤ t ∧ (s + 2) % 2 = t % 2 := by
            constructor <;> omega
          simp only [h, h', hts, ite_false, sub_self]
        · have h' : ¬(s + 2 ≤ t ∧ (s + 2) % 2 = t % 2) := by
            intro hh
            exact h ⟨by omega, by omega⟩
          simp only [h, h', hts, ite_false, sub_self]
    _ = originalFactor N s := by simp [hs]

/-- The unnormalized positive-factor candidate, computed by reverse parity sums. -/
def factor (N s : ℕ) : ℝ[X] :=
  C (1 / omega N s) * tail N s - C (1 / omega N (s + 2)) * tail N (s + 2)

/-- Exact separated factorization for every pair of real spectral coordinates. -/
theorem factorization (N : ℕ) (hN : 2 ≤ N) (x y : ℝ) :
    ∑ s ∈ Finset.range N, (factor N s).eval x * (psi N s).eval y =
      chebyshevBezout N x y := by
  have ht : ∀ s, N ≤ s → (tail N s).eval x = 0 := by
    intro s hs
    rw [tail_eq_zero hs, eval_zero]
  have hp := parity_transform N hN (fun s => (tail N s).eval x) ht y
  simp only [factor, eval_sub, eval_mul, eval_C, one_div_mul_eq_div] at ⊢
  rw [hp]
  have ho :
      (∑ s ∈ Finset.range N,
        ((tail N s).eval x - (tail N (s + 2)).eval x) * (T ℝ s).eval y) =
      ∑ s ∈ Finset.range N, (originalFactor N s).eval x * (T ℝ s).eval y := by
    apply Finset.sum_congr rfl
    intro s hs
    rw [← eval_sub, tail_sub_add_two (Finset.mem_range.mp hs)]
  rw [ho]
  have hn : N - 1 + 1 = N := by omega
  have he := hall_expansion (N - 1) y x
  rw [hn] at he
  have hsym : chebyshevBezout N y x = chebyshevBezout N x y := by
    unfold chebyshevBezout History.dividedDifference
    by_cases hxy : x = y
    · subst y; rfl
    · simp only [hxy, Ne.symm hxy, ite_false]
      congr 1
      field_simp
      ring
  rw [hsym] at he
  rw [he]
  unfold hallSum
  rw [hn]
  apply Finset.sum_congr rfl
  intro s _
  by_cases hs : s = 0
  · simp [originalFactor, hallTerm, hallWeight, hs]
  · simp [originalFactor, hallTerm, hallWeight, hs, mul_comm]

end
end bezout.Balanced
