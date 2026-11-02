import bezout.Balanced.Tails

/-!
Article: bezout, nonnegativity of the response factor in Equation `eq:V`.
Use: the exact parity weights retain enough leading Chebyshev mass to dominate
all later same-parity second-kind polynomials.
Proof: the number of later terms is at most half the remaining degree; the
four parity formulas then reduce to real polynomial inequalities.
-/

namespace bezout.Balanced
noncomputable section

/-- A parity tail after one more step contains at most half the remaining degree. -/
theorem parityLength_bound {N s : ℕ} (hs : s + 2 < N) :
    2 * (parityLength N (s + 2) : ℝ) ≤ (N : ℝ) - 1 - s := by
  have hn : 2 * parityLength N (s + 2) + 1 + s ≤ N := by
    unfold parityLength
    omega
  have hr : 2 * (parityLength N (s + 2) : ℝ) + 1 + s ≤ N := by exact_mod_cast hn
  linarith

/-- The leading Hall coefficient dominates the loss from every later parity term. -/
theorem omega_tail_ratio {N s : ℕ} (hN : 2 ≤ N) (hs : s + 2 < N) :
    (parityLength N (s + 2) : ℝ) * (omega N s - omega N (s + 2)) ≤
      hallWeight s * omega N (s + 2) := by
  have hn : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hsr : (s : ℝ) + 2 < N := by exact_mod_cast hs
  have hk := parityLength_bound hs
  have hk0 : (0 : ℝ) ≤ parityLength N (s + 2) := by positivity
  have hm : (s + 2) % 2 = s % 2 := by omega
  have hp : Even (s + 2) ↔ Even s := by simp [Nat.even_add]
  have hl : ¬s + 2 < 2 := by omega
  by_cases hz : s = 0
  · subst s
    norm_num only [omega_zero, omega, hallWeight, Nat.reduceAdd, Nat.reduceLT,
      Nat.reduceMod, Nat.cast_ofNat, even_two, ite_true, ite_false]
    split_ifs with he
    · field_simp
      nlinarith
    · field_simp
      have hh := mul_nonneg hk0 (show 0 ≤ (N : ℝ) ^ 2 - 1 by nlinarith)
      nlinarith [sq_nonneg ((N : ℝ) - 2)]
  · by_cases ho : s = 1
    · subst s
      norm_num only [Nat.reduceAdd, Nat.cast_one] at hk hk0
      norm_num only [omega_one, omega, hallWeight, Nat.reduceAdd, Nat.reduceLT,
        Nat.reduceMod, Nat.cast_ofNat, Nat.not_even_one, ite_true, ite_false]
      split_ifs with he
      · field_simp
        nlinarith
      · field_simp
        nlinarith
    · have hsmall : ¬s < 2 := by omega
      have hmod : ((s % 2 : ℕ) : ℝ) = if Even s then 0 else 1 := by
        by_cases he : Even s
        · simp [he, Nat.even_iff.mp he]
        · simp [he, Nat.not_even_iff.mp he]
      simp only [omega, hallWeight, hz, ite_false, hsmall, hl, hm, hp,
        Nat.cast_add, Nat.cast_ofNat]
      rw [hmod]
      split_ifs with he hp'
      all_goals field_simp
      all_goals nlinarith

end
end bezout.Balanced
