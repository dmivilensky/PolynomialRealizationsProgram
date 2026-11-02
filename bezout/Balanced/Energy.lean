import bezout.Balanced.Masses
import bezout.Lower.EndpointGain

/-!
Article: bezout, the exact gain calculation in Theorem `thm:linear`.
Use: proves the squared parity product masses equal the exact even/odd optimum.
Proof: finite parity counting and real algebra; the odd correction is retained.
-/

namespace bezout.Balanced
noncomputable section
open scoped BigOperators

/-- Finite parity counting with arbitrary real values on the two classes. -/
theorem sum_parity (N : ℕ) (A B : ℝ) :
    (∑ s ∈ Finset.range N, if Even s then A else B) =
      (((N + 1) / 2 : ℕ) : ℝ) * A + ((N / 2 : ℕ) : ℝ) * B := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    by_cases h : Even N
    · have hp := Nat.even_iff.mp h
      have h1 : (N + 1 + 1) / 2 = (N + 1) / 2 + 1 := by omega
      have h2 : (N + 1) / 2 = N / 2 := by omega
      simp only [h, ite_true, h1, h2, Nat.cast_add, Nat.cast_one]
      ring
    · have hp := Nat.not_even_iff.mp h
      have h1 : (N + 1 + 1) / 2 = (N + 1) / 2 := by omega
      have h2 : (N + 1) / 2 = N / 2 + 1 := by omega
      simp only [h, ite_false, h1, h2, Nat.cast_add, Nat.cast_one]
      ring

/-- Every class mass is positive on the article's horizon domain. -/
theorem classMass_pos {N s : ℕ} (hN : 2 ≤ N) : 0 < classMass N s := by
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  unfold classMass
  split_ifs <;> positivity

/-- The sum of squared product masses is exactly the normalized optimal energy. -/
theorem classMass_energy {N : ℕ} (hN : 2 ≤ N) :
    (∑ s ∈ Finset.range N, classMass N s ^ 2) =
      (N : ℝ) ^ 3 / 4 * Lower.linearCorrectionSq N := by
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  by_cases he : Even N
  · have hodd : ¬Odd N := by simpa [Nat.not_odd_iff_even] using he
    simp [classMass, he, Lower.linearCorrectionSq, hodd, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul]
    ring
  · have hodd : Odd N := Nat.not_even_iff_odd.mp he
    have hp := Nat.not_even_iff.mp he
    have hsum : (∑ s ∈ Finset.range N, classMass N s ^ 2) =
        (((N + 1) / 2 : ℕ) : ℝ) * (((N : ℝ) ^ 2 + 1) / (2 * ((N : ℝ) + 1))) ^ 2 +
        ((N / 2 : ℕ) : ℝ) * (((N : ℝ) + 1) / 2) ^ 2 := by
      rw [← sum_parity]
      apply Finset.sum_congr rfl
      intro s _
      simp only [classMass, he, ite_false]
      split_ifs <;> rfl
    rw [hsum]
    have hc1 : 2 * ((N + 1) / 2) = N + 1 := by omega
    have hc0 : 2 * (N / 2) = N - 1 := by omega
    have hr1 : (((N + 1) / 2 : ℕ) : ℝ) = ((N : ℝ) + 1) / 2 := by
      have hh : 2 * (((N + 1) / 2 : ℕ) : ℝ) = (N : ℝ) + 1 := by exact_mod_cast hc1
      linarith
    have hr0 : ((N / 2 : ℕ) : ℝ) = ((N : ℝ) - 1) / 2 := by
      have hc : 2 * (N / 2) + 1 = N := by omega
      have hh : 2 * ((N / 2 : ℕ) : ℝ) + 1 = N := by exact_mod_cast hc
      linarith
    rw [hr1, hr0]
    simp only [Lower.linearCorrectionSq, hodd, ite_true, Lower.oddCorrectionSq]
    field_simp
    ring

/-- The physical scaling turns the exact parity energy into the squared sharp gain. -/
theorem scaled_classMass_energy (I : chebyshev1.SpectralInterval) {N : ℕ}
    (hN : 2 ≤ N) :
    (∑ s ∈ Finset.range N, (4 * I.epsilon N / I.delta * classMass N s) ^ 2) =
      Lower.linearGain I N ^ 2 := by
  simp only [mul_pow, ← Finset.mul_sum]
  rw [classMass_energy hN, Lower.linearGain_sq I hN]
  unfold Lower.derivativeScale
  field_simp
  ring

end
end bezout.Balanced
