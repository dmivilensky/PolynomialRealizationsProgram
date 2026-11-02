import Mathlib.Tactic

/-!
Article: bezout, Equation `eq:stopped-D` and Algorithm 2 scalar preparation.
Use: the exact positive parity weights determine the Balanced query basis.
All subtractions in the formulas are real subtractions; horizon bounds are
proved before these weights are used as denominators.
-/

namespace bezout.Balanced

noncomputable section

/-- The exact stopped-parity weight, including both initial weights. -/
def omega (N s : ℕ) : ℝ :=
  if s < 2 then 1 else
    if Even N then ((N : ℝ) + 2 - s - (s % 2 : ℕ)) / N else
      if Even s then ((N : ℝ) + 1) * ((N : ℝ) + 1 - s) / ((N : ℝ) ^ 2 + 1)
      else ((N : ℝ) + 2 - s) / ((N : ℝ) + 1)

/-- The first query weight is exactly one. -/
@[simp] theorem omega_zero (N : ℕ) : omega N 0 = 1 := by simp [omega]

/-- The second query weight is exactly one. -/
@[simp] theorem omega_one (N : ℕ) : omega N 1 = 1 := by simp [omega]

/-- Every weight used by a valid physical call is strictly positive. -/
theorem omega_pos {N s : ℕ} (hN : 2 ≤ N) (hs : s < N) : 0 < omega N s := by
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hsr : (s : ℝ) < N := by exact_mod_cast hs
  have hmod : (s % 2 : ℕ) < 2 := Nat.mod_lt _ (by omega)
  have hmr : ((s % 2 : ℕ) : ℝ) < 2 := by exact_mod_cast hmod
  unfold omega
  split_ifs
  · norm_num
  · apply div_pos _ (by positivity)
    linarith
  · apply div_pos (mul_pos (by positivity) (by linarith)) (by positivity)
  · apply div_pos (by linarith) (by positivity)

/-- The initial convex mass remains at least the current top-degree weight. -/
theorem omega_le_one {N s : ℕ} (hN : 2 ≤ N) (_hs : s < N) : omega N s ≤ 1 := by
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hs2 : ¬s < 2 → (2 : ℝ) ≤ s := by intro h; exact_mod_cast (show 2 ≤ s by omega)
  have hmod : (0 : ℝ) ≤ (s % 2 : ℕ) := by positivity
  unfold omega
  split_ifs with hsmall heven hpar
  · rfl
  · apply (div_le_iff₀ (show (0 : ℝ) < N by linarith)).mpr
    have := hs2 hsmall
    linarith
  · apply (div_le_iff₀ (show 0 < (N : ℝ) ^ 2 + 1 by positivity)).mpr
    have hs' := hs2 hsmall
    have hp := mul_nonneg (show 0 ≤ (N : ℝ) + 1 by positivity) (show 0 ≤ (s : ℝ) - 2 by linarith)
    nlinarith
  · apply (div_le_iff₀ (show 0 < (N : ℝ) + 1 by positivity)).mpr
    have := hs2 hsmall
    linarith

/-- Weights decrease along each parity class, including its initial weight. -/
theorem omega_add_two_le {N s : ℕ} (hN : 2 ≤ N) (hs : s + 2 < N) :
    omega N (s + 2) ≤ omega N s := by
  by_cases hsmall : s < 2
  · have heq : omega N s = 1 := by simp [omega, hsmall]
    rw [heq]
    exact omega_le_one hN hs
  · have hlarge : ¬s + 2 < 2 := by omega
    have hp : Even (s + 2) ↔ Even s := by simp [Nat.even_add]
    have hm : (s + 2) % 2 = s % 2 := by omega
    have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
    unfold omega
    simp only [hsmall, hlarge, ite_false, hp, hm, Nat.cast_add, Nat.cast_ofNat]
    split_ifs with heven hpar
    · apply (div_le_div_iff_of_pos_right (show (0 : ℝ) < N by linarith)).mpr
      linarith
    · apply (div_le_div_iff_of_pos_right (show 0 < (N : ℝ) ^ 2 + 1 by positivity)).mpr
      have hn : 0 ≤ (N : ℝ) + 1 := by positivity
      nlinarith
    · apply (div_le_div_iff_of_pos_right (show 0 < (N : ℝ) + 1 by positivity)).mpr
      linarith

end
end bezout.Balanced
