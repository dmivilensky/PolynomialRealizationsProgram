import bezout.Balanced.Tails

/-!
Article: bezout, Equation `eq:linear-balance`.
Use: exact parity masses of the genuinely constructed Balanced response factors.
Proof: divide the explicit finite tail masses by the exact parity weights;
consecutive quotients differ by one common class mass.
-/

namespace bezout.Balanced
noncomputable section
open Polynomial Polynomial.Chebyshev

/-- The exact common product mass in each parity class. -/
def classMass (N s : ℕ) : ℝ :=
  if Even N then (N : ℝ) / 2 else
    if Even s then ((N : ℝ) ^ 2 + 1) / (2 * ((N : ℝ) + 1)) else ((N : ℝ) + 1) / 2

/-- Same-parity remaining degree gives an exact even tail count. -/
theorem parityLength_same {N s : ℕ} (hs : s < N) (hp : N % 2 = s % 2) :
    2 * parityLength N s + s = N := by unfold parityLength; omega

/-- Opposite-parity remaining degree gives an exact odd tail count. -/
theorem parityLength_opposite {N s : ℕ} (hs : s < N) (hp : N % 2 ≠ s % 2) :
    2 * parityLength N s + s = N + 1 := by unfold parityLength; omega

/-- Each nonempty tail quotient is its length times the common parity mass. -/
theorem tail_quotient {N s : ℕ} (hN : 2 ≤ N) (hs : s < N) :
    (tail N s).eval 1 / omega N s = (parityLength N s : ℝ) * classMass N s := by
  have hm : 0 < parityLength N s := by unfold parityLength; omega
  have hmr : (0 : ℝ) < parityLength N s := by exact_mod_cast hm
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have heven : Even N → N % 2 = 0 := Nat.even_iff.mp
  have hodd : ¬Even N → N % 2 = 1 := Nat.not_even_iff.mp
  rw [tail_eval_one hs]
  by_cases hz : s = 0
  · subst s
    rw [omega_zero]
    simp only [classMass, show Even (0 : ℕ) by decide, ite_true, Nat.cast_zero, sub_zero, div_one]
    split_ifs with he
    · have hc := parityLength_same hs (by simpa using heven he)
      have hcr : (N : ℝ) = 2 * parityLength N 0 := by exact_mod_cast hc.symm
      rw [hcr]
      ring
    · have hc := parityLength_opposite hs (by simp [hodd he])
      have hcr : (N : ℝ) = 2 * parityLength N 0 - 1 := by
        have hh : 2 * (parityLength N 0 : ℝ) = (N : ℝ) + 1 := by exact_mod_cast hc
        linarith
      rw [hcr]
      ring_nf
      field_simp (disch := positivity)
  · by_cases ho : s = 1
    · subst s
      rw [omega_one]
      simp only [classMass, Nat.not_even_one, ite_false, Nat.cast_one,
        sub_zero, hz, div_one]
      split_ifs with he
      · have hc := parityLength_opposite hs (by simp [heven he])
        have hcr : (N : ℝ) = 2 * parityLength N 1 := by
          have hh : 2 * (parityLength N 1 : ℝ) + 1 = (N : ℝ) + 1 := by exact_mod_cast hc
          linarith
        rw [hcr]
        ring
      · have hc := parityLength_same hs (by simp [hodd he])
        have hcr : (N : ℝ) = 2 * parityLength N 1 + 1 := by exact_mod_cast hc.symm
        rw [hcr]
        ring
    · have hsmall : ¬s < 2 := by omega
      have hsEven : Even s → s % 2 = 0 := Nat.even_iff.mp
      have hsOdd : ¬Even s → s % 2 = 1 := Nat.not_even_iff.mp
      simp only [omega, hsmall, ite_false, classMass, hz]
      split_ifs with he hp
      · by_cases hp : Even s
        · have hc := parityLength_same hs (by simp [heven he, hsEven hp])
          have hcr : (s : ℝ) = (N : ℝ) - 2 * parityLength N s := by
            have hh : 2 * (parityLength N s : ℝ) + s = N := by exact_mod_cast hc
            linarith
          rw [hsEven hp, Nat.cast_zero, hcr]
          ring_nf
          field_simp (disch := positivity)
          all_goals ring
        · have hc := parityLength_opposite hs (by simp [heven he, hsOdd hp])
          have hcr : (s : ℝ) = (N : ℝ) + 1 - 2 * parityLength N s := by
            have hh : 2 * (parityLength N s : ℝ) + s = (N : ℝ) + 1 := by exact_mod_cast hc
            linarith
          rw [hsOdd hp, Nat.cast_one, hcr]
          ring_nf
          field_simp (disch := positivity)
      · have hc := parityLength_opposite hs (by simp [hodd he, hsEven hp])
        have hcr : (s : ℝ) = (N : ℝ) + 1 - 2 * parityLength N s := by
          have hh : 2 * (parityLength N s : ℝ) + s = (N : ℝ) + 1 := by exact_mod_cast hc
          linarith
        rw [hcr]
        ring_nf
        field_simp (disch := positivity)
        all_goals ring
      · have hc := parityLength_same hs (by simp [hodd he, hsOdd hp])
        have hcr : (s : ℝ) = (N : ℝ) - 2 * parityLength N s := by
          have hh : 2 * (parityLength N s : ℝ) + s = N := by exact_mod_cast hc
          linarith
        rw [hcr]
        ring_nf
        field_simp (disch := positivity)
        all_goals ring

/-- Exact parity factor masses, including both startup calls and terminal calls. -/
theorem factor_eval_one {N s : ℕ} (hN : 2 ≤ N) (hs : s < N) :
    (factor N s).eval 1 = classMass N s := by
  simp only [factor, eval_sub, eval_mul, eval_C, one_div_mul_eq_div]
  rw [tail_quotient hN hs]
  by_cases ht : s + 2 < N
  · rw [tail_quotient hN ht]
    have hl : parityLength N s = parityLength N (s + 2) + 1 := by
      unfold parityLength
      omega
    have hc : classMass N (s + 2) = classMass N s := by
      simp [classMass, Nat.even_add]
    rw [hc, hl]
    push_cast
    ring
  · rw [tail_eq_zero (by omega), eval_zero, zero_div, sub_zero]
    have hl : parityLength N s = 1 := by unfold parityLength; omega
    simp [hl]

end
end bezout.Balanced
