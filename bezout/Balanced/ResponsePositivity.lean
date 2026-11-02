import bezout.Balanced.Ratio
import bezout.Balanced.Positive

/-!
Article: bezout, positive response factorization in Theorem `thm:linear`.
Use: proves positivity of the constructed responses by an explicit alternative
to matrix inversion. Each later second-kind term is dominated coefficientwise
by the leading term of the same parity.
-/

namespace bezout.Balanced
noncomputable section
open Polynomial Polynomial.Chebyshev
open scoped BigOperators

/-- The half-weight at the first Hall coefficient is always positive. -/
theorem hallWeight_pos (s : ℕ) : 0 < hallWeight s := by
  unfold hallWeight
  split_ifs <;> norm_num

/-- All reverse parity tail terms after the first index have unit Hall weight. -/
theorem tail_add_two_range {N s : ℕ} (hs : s + 2 < N) :
    tail N (s + 2) = ∑ j ∈ Finset.range (parityLength N (s + 2)),
      U ℝ ((N - 1 - ((s + 2) + 2 * j) : ℕ) : ℤ) := by
  rw [tail_range hs]
  apply Finset.sum_congr rfl
  intro j _
  simp [originalFactor, hallWeight]

/-- Every unnormalized Balanced response has nonnegative Chebyshev coefficients. -/
theorem factor_positive {N s : ℕ} (hN : 2 ≤ N) (hs : s < N) :
    ChebPositive (factor N s) := by
  have hds := omega_pos hN hs
  have hdecomp : tail N s = originalFactor N s + tail N (s + 2) :=
    sub_eq_iff_eq_add.mp (tail_sub_add_two hs)
  by_cases ht : s + 2 < N
  · have hdt := omega_pos hN ht
    let K := parityLength N (s + 2)
    let beta := 1 / omega N (s + 2) - 1 / omega N s
    let alpha := hallWeight s / omega N s - beta * K
    have hbeta : 0 ≤ beta := by
      exact sub_nonneg.mpr (one_div_le_one_div_of_le hdt (omega_add_two_le hN ht))
    have halpha : 0 ≤ alpha := by
      have hr := omega_tail_ratio hN ht
      have ha : alpha = (hallWeight s * omega N (s + 2) -
          (omega N s - omega N (s + 2)) * K) / (omega N s * omega N (s + 2)) := by
        dsimp [alpha, beta]
        field_simp
      rw [ha]
      exact div_nonneg (by dsimp [K]; nlinarith) (mul_pos hds hdt).le
    let S : ℝ[X] := ∑ j ∈ Finset.range K,
      (U ℝ ((N - 1 - s : ℕ) : ℤ) - U ℝ ((N - 1 - ((s + 2) + 2 * j) : ℕ) : ℤ))
    have hS : ChebPositive S := by
      apply ChebPositive.sum
      intro j hj
      have hj' : j < K := Finset.mem_range.mp hj
      have hlt : (s + 2) + 2 * j < N := by
        dsimp [K] at hj'
        unfold parityLength at hj'
        omega
      apply U_sub_positive <;> omega
    have he : factor N s = C alpha * U ℝ ((N - 1 - s : ℕ) : ℤ) + C beta * S := by
      rw [factor, hdecomp, tail_add_two_range ht]
      dsimp only [alpha, beta, K, S]
      simp only [originalFactor, Finset.sum_sub_distrib, Finset.sum_const,
        Finset.card_range, nsmul_eq_mul, div_eq_mul_inv, one_mul,
        Polynomial.C_sub, Polynomial.C_mul, Polynomial.C_eq_natCast]
      ring
    rw [he]
    exact ChebPositive.add (ChebPositive.scale alpha halpha (U_positive _))
      (ChebPositive.scale beta hbeta hS)
  · have hz := tail_eq_zero (N := N) (s := s + 2) (by omega)
    rw [factor, hz, hdecomp, hz]
    simp only [mul_zero, sub_zero, add_zero, originalFactor]
    rw [← mul_assoc, ← Polynomial.C_mul]
    exact ChebPositive.scale _ (mul_nonneg (one_div_pos.mpr hds).le (hallWeight_pos s).le)
      (U_positive _)

/-- The exact endpoint mass bounds the response at every spectral coordinate. -/
theorem factor_bound {N s : ℕ} (hN : 2 ≤ N) (hs : s < N) {x : ℝ}
    (hx : |x| ≤ 1) : |(factor N s).eval x| ≤ (factor N s).eval 1 :=
  (factor_positive hN hs).bound hx

end
end bezout.Balanced
